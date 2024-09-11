require import List Int IntDiv CoreMap Ring StdOrder W64limbs StdBigop BitEncoding.
from Jasmin require import JModel JWord JWord_array.
import Ring.IntID IntOrder StdBigop.Bigint.BIA BitEncoding.BS2Int.

lemma foldl_in_eq_r (f1 : 'a1 -> 'b -> 'a1)
    (f2 : 'a2 -> 'b -> 'a2)
    (s  : 'b list)
    (a2 : 'a2)
    (r  : 'a2 -> 'a1) :
    (forall a2 b, b \in s => f1 (r a2) b = r (f2 a2 b)) =>
                        foldl f1 (r a2) s = r (foldl f2 a2 s).
proof.
    move: s a2. elim. by move => a2.
    move => x l hrec a2 /= hin. rewrite hin.
    by left.
    rewrite hrec //; move => ? ? h; rewrite hin.
    by right.
    by trivial.
qed.

lemma ltr_pmul2 x1 x2 y1 y2:
    0 <= x1 => 0 <= x2 => x1 < y1 => x2 < y2 => x1 * x2 < y1 * y2 by smt().

lemma divzU a b q r:
    0 <= r < `|b|%Int => a = b * q + r => q = a%/b by smt().

lemma divz_div a b c:
    0 < b => 0 < c => a %/ b %/ c = a %/ (b * c).
proof.
    move=> *.
    apply (divzU _ _ _ (b * ((a %/ b) %%c) + a %% b)).
    split; smt(). smt().
qed.

lemma modz_minus x d:
    (d <= x < 2 * d)%Int => x %% d = x - d by smt().

lemma iota_split len2 n len:
    0 <= len2 <= len => iota_ n len = iota_ n len2 ++ iota_ (n+len2) (len-len2).
proof.
    move=> H. have E: len = len2 + (len - len2) by smt().
    by rewrite {1} E iota_add // /#.
qed.

(* different views on datatypes *)
lemma of_int2u64 i0 i1:
    pack2 [ W64.of_int i0; W64.of_int i1 ] = W128.of_int (i0 %% W64.modulus + W64.modulus * i1).
proof.
    rewrite W2u64.of_uint_pack2 -iotaredE /=; congr; congr => />. split.
    apply W64.word_modeqP; congr.
        by rewrite !of_uintK mulzC modzMDr !modz_mod.
    rewrite mulzC divzMDr //.
    have ->:i0 %% 18446744073709551616 %/ 18446744073709551616 = 0 by smt(modz_cmp divz_eq0).
    by rewrite !of_intE modz_mod.
qed.

lemma to_uint_unpack2u64 w:
    W128.to_uint w = val_digits W64.modulus (map W64.to_uint (W2u64.to_list w)).
proof.
    have [? /= ?]:= W128.to_uint_cmp w.
    rewrite /val_digits /=.
    do 2! (rewrite bits64_div 1:// /=).
    rewrite !of_uintK /=.
    have P: forall x, x = x %% 18446744073709551616 + 18446744073709551616 * (x %/ 18446744073709551616).
        by move=> x; rewrite {1}(divz_eq x 18446744073709551616) /=; ring.
    rewrite {1}(P (to_uint w)) {1}(P (to_uint w %/ 18446744073709551616)) divz_div 1..2:/# /=.
    by ring; smt().
qed.

lemma to_uint2u64 w0 w1:
    to_uint (W2u64.pack2 [w0; w1]) = to_uint w0 + W64.modulus * to_uint w1.
proof.
    by rewrite to_uint_unpack2u64.
qed.

lemma to_uint_unpack4u32 w:
    W128.to_uint w = val_digits W32.modulus (map W32.to_uint (W4u32.to_list w)).
proof.
    have [? /= ?]:= W128.to_uint_cmp w.
    rewrite /val_digits /=.
    do 4! (rewrite bits32_div 1:// /=).
    rewrite !of_uintK /=.
    have P: forall x, x = x %% 4294967296 + 4294967296 * (x %/ 4294967296).
        by move=> x; rewrite {1}(divz_eq x 4294967296) /=; ring.
    rewrite {1}(P (to_uint w)) {1}(P (to_uint w %/ 4294967296)) divz_div 1..2:/#
            {1}(P (to_uint w %/ 18446744073709551616)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 79228162514264337593543950336)) divz_div 1..2:/# /=.
    by ring; smt().
qed.

lemma to_uint_unpack16u8 w:
    W128.to_uint w = val_digits W8.modulus (map W8.to_uint (W16u8.to_list w)).
proof.
    have [? /= ?]:= W128.to_uint_cmp w.
    rewrite /val_digits /=.
    do 16! (rewrite bits8_div 1:// /=).
    have P: forall x, x = x %% 256 + 256 * (x %/ 256).
     by move=> x; rewrite {1}(divz_eq x W8.modulus) /=; ring.
    rewrite {1}(P (to_uint w)) {1}(P (to_uint w %/ 256)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 65536)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 16777216)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 4294967296)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 1099511627776)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 281474976710656)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 72057594037927936)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 18446744073709551616)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 4722366482869645213696)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 1208925819614629174706176)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 309485009821345068724781056)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 79228162514264337593543950336)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 20282409603651670423947251286016)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 5192296858534827628530496329220096)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 1329227995784915872903807060280344576)) divz_div 1..2:/# /=.
    ring; smt().
qed.

lemma to_uint_unpack8u8 w:
    W64.to_uint w = val_digits W8.modulus (map W8.to_uint (W8u8.to_list w)).
proof.
    have [? /= ?]:= W64.to_uint_cmp w.
    rewrite /val_digits /=.
    do 8! (rewrite bits8_div 1:// /=).
    have P: forall x, x = x %% 256 + 256 * (x %/ 256).
        by move=> x; rewrite {1}(divz_eq x 256) /=; ring.
    rewrite {1}(P (to_uint w)) {1}(P (to_uint w %/ 256)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 65536)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 16777216)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 4294967296)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 1099511627776)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 281474976710656)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 72057594037927936)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 18446744073709551616)) divz_div 1..2:/# /=.
    ring; smt().
qed.

lemma to_uint_unpack32u8 w:
    W256.to_uint w = val_digits W8.modulus (map W8.to_uint (W32u8.to_list w)).
proof.
    have [? /= ?]:= W256.to_uint_cmp w.
    rewrite /val_digits /=.
    do 32! (rewrite bits8_div 1:// /=).
    have P: forall x, x = x %% 256 + 256 * (x %/ 256).
        by move=> x; rewrite {1}(divz_eq x W8.modulus) /=; ring.
    rewrite {1}(P (to_uint w)) {1}(P (to_uint w %/ 256)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 65536)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 16777216)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 4294967296)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 1099511627776)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 281474976710656)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 72057594037927936)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 18446744073709551616)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 4722366482869645213696)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 1208925819614629174706176)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 309485009821345068724781056)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 79228162514264337593543950336)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 20282409603651670423947251286016)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 5192296858534827628530496329220096)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 1329227995784915872903807060280344576)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 340282366920938463463374607431768211456)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 87112285931760246646623899502532662132736)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 22300745198530623141535718272648361505980416)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 5708990770823839524233143877797980545530986496)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 1461501637330902918203684832716283019655932542976)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 374144419156711147060143317175368453031918731001856)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 95780971304118053647396689196894323976171195136475136)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 24519928653854221733733552434404946937899825954937634816)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 6277101735386680763835789423207666416102355444464034512896)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 1606938044258990275541962092341162602522202993782792835301376)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 411376139330301510538742295639337626245683966408394965837152256)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 105312291668557186697918027683670432318895095400549111254310977536)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 26959946667150639794667015087019630673637144422540572481103610249216)) divz_div 1..2:/# /=.
    rewrite {1}(P (to_uint w %/ 6901746346790563787434755862277025452451108972170386555162524223799296)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 1766847064778384329583297500742918515827483896875618958121606201292619776)) divz_div 1..2:/# /=
            {1}(P (to_uint w %/ 452312848583266388373324160190187140051835877600158453279131187530910662656)) divz_div 1..2:/# /=.
    ring; smt().
qed.

lemma to_uint_unpack4u64 w:
    W256.to_uint w = val_digits W64.modulus (map W64.to_uint (W4u64.to_list w)).
proof.
    have [? /= ?]:= W256.to_uint_cmp w.
    rewrite /val_digits /=.
    do 4! (rewrite bits64_div 1:// /=).
    rewrite !of_uintK /=.
    have P: forall x, x = x %% 18446744073709551616 + 18446744073709551616 * (x %/ 18446744073709551616).
        by move=> x; rewrite {1}(divz_eq x 18446744073709551616) /=; ring.
    rewrite {1}(P (to_uint w)) {1}(P (to_uint w %/ 18446744073709551616)) divz_div 1..2:/# /=
            {1}(P (to_uint w)) {1}(P (to_uint w %/  340282366920938463463374607431768211456)) divz_div 1..2:/# /=
            {1}(P (to_uint w)) {1}(P (to_uint w %/ 6277101735386680763835789423207666416102355444464034512896)) divz_div 1..2:/# /=.
     by ring; smt().
qed.

lemma pack8u8_init_mkseq f:
    pack8_t (init f)%W8u8.Pack = pack8 (mkseq f 8).
proof.
    by rewrite W8u8.Pack.init_of_list.
qed.

lemma load8u8' mem p:
    loadW64 mem p = pack8 (mkseq (fun i => mem.[p+i]) 8).
proof.
    rewrite /mkseq /= /loadW64 -iotaredE; congr => />.
    rewrite W8u8.Pack.init_of_list -iotaredE. by congr => />.
qed.
