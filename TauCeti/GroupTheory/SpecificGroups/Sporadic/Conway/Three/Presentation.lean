/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Conway.Three.Basic

/-!
# Presentation homomorphism onto the ATLAS model of the third Conway group

This file connects Djoković's seven-involution presentation `TauCeti.Sporadic.co3Presentation`
(carried by `TauCeti.SporadicName.Co3.presentation`) to the degree-276 ATLAS permutation model
`TauCeti.Sporadic.Co3`.

Seven explicit involutions in `Equiv.Perm (Fin 276)` are assigned to the seven generators
`a, b, c, d, e, f, g` of presentation (13.1) via `TauCeti.Sporadic.Co3.presentationImage`. Every
transcribed relator evaluates to `1` in Mathlib's right-to-left composition convention. Explicit
words in the ATLAS generators `Co3.a`, `Co3.b`, and their inverses place the images of `a`, `b`,
`c`, `d`, and `g` in `Co3`, while the relators `f (a g)³ = 1` and `e (a b c)³ = 1` place the images
of `f` and `e` in `Co3`. Conversely, short words in the seven involutions recover `Co3.a` and
`Co3.b`, so the images generate exactly `Co3`.

Lifting the assignment via `TauCeti.GroupPresentation.homEquiv` produces
`TauCeti.Sporadic.Co3.presentationHom` with range `Co3`, giving the surjection
`TauCeti.Sporadic.exists_surjective_Co3` and nontriviality of `TauCeti.SporadicName.Co3.Group`. No
finiteness, order, or isomorphism of the presented group is asserted here.

## Main definitions

* `TauCeti.Sporadic.Co3.presentationImage`: the seven involutions in `Co3` assigned to Djoković's
  generators.
* `TauCeti.Sporadic.Co3.presentationHom`: the homomorphism from `TauCeti.SporadicName.Co3.Group`
  into `Equiv.Perm (Fin 276)`.

## Main results

* `TauCeti.Sporadic.Co3.presentationImage_mem`: every generator image lies in `Co3`.
* `TauCeti.Sporadic.Co3.orderOf_presentationImage`: every generator image has order two.
* `TauCeti.Sporadic.Co3.lift_presentationImage_toFreeGroup_eq_one`: all twenty-four transcribed
  relators hold at `presentationImage`.
* `TauCeti.Sporadic.Co3.closure_range_presentationImage`: the images generate `Co3`.
* `TauCeti.Sporadic.Co3.range_presentationHom`: the range of `presentationHom` is `Co3`.
* `TauCeti.Sporadic.exists_surjective_Co3`: the presented group of `Co₃` maps surjectively onto
  `Co3`.

## References

* D. Ž. Djoković, *Presentations of some finite simple groups*, J. Austral. Math. Soc. Ser. A
  **45** (1988), 143--168, presentation (13.1), p. 162,
  <https://doi.org/10.1017/S1446788700030068>.
* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `Co3G1-p276B0`, <https://brauer.maths.qmul.ac.uk/Atlas/v3/>.
-/

public section

namespace TauCeti.Sporadic

namespace Co3

/-! ### Bit-packed permutation tables -/

/- Eight 315-bit natural numbers pack the 276 images at 9 bits per entry (35 entries per block).
Shift-and-modulus lookup reduces directly in `ℕ` via kernel arithmetic without traversing array
spines or wrapping intermediate values in `Fin`. -/
private def chunkLookupNat (c0 c1 c2 c3 c4 c5 c6 c7 : ℕ) (i : ℕ) : ℕ :=
  let blk := match i / 35 with
    | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | 6 => c6 | _ => c7
  (blk >>> ((i % 35) * 9)) % 512

private def packedInvol (c0 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (hf : ∀ i : Fin 276, chunkLookupNat c0 c1 c2 c3 c4 c5 c6 c7 i.val < 276)
    (hff : ∀ i : Fin 276,
      chunkLookupNat c0 c1 c2 c3 c4 c5 c6 c7
        (chunkLookupNat c0 c1 c2 c3 c4 c5 c6 c7 i.val) = i.val) :
    Equiv.Perm (Fin 276) :=
  Function.Involutive.toPerm
    (fun i : Fin 276 ↦ ⟨chunkLookupNat c0 c1 c2 c3 c4 c5 c6 c7 i.val, hf i⟩)
    fun i ↦ Fin.ext (hff i)

private theorem packedInvol_sq (c0 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (hf : ∀ i : Fin 276, chunkLookupNat c0 c1 c2 c3 c4 c5 c6 c7 i.val < 276)
    (hff : ∀ i : Fin 276,
      chunkLookupNat c0 c1 c2 c3 c4 c5 c6 c7
        (chunkLookupNat c0 c1 c2 c3 c4 c5 c6 c7 i.val) = i.val) :
    packedInvol c0 c1 c2 c3 c4 c5 c6 c7 hf hff ^ 2 = 1 := by
  rw [packedInvol, sq]
  exact Equiv.ext (Function.Involutive.toPerm_involutive _)

/- Bit-packed copies of the ATLAS generators `a` and `b`, checked once against `Co3.a` and `Co3.b`,
keep the word evaluations below fast in the kernel. -/
private def aFastFun : ℕ → ℕ :=
  chunkLookupNat
    0x2649e411d848087d750b044ed6807c06853d19054ff4f05610b95d0281283252ec0c82071bc52f4
    0x3f8aa430bb44f23412b98fc16491cc909b25af8d8eb55b945c9a5ac11b90e53158b87523334e8fa
    0x1f0ce32390786a0f833e0d04449aa53a5979401f2012f1515ab404354e30523bed946e0a25114c3
    0x4049ad8710314e49471443a100e2f578802f82e18a86fbc1d8b3502415c21704240ecb1f8b4b6da
    0x1958ef5333a0504064044ec3315c3c30247e188d51181bdc323136930d2386b441fa3948b8d62db
    0x0808502468f918971b1810c5367b487a263c2a8c24531c2c78053da1c004e850c1bc274e3398a9f
    0x2e0b05a283a512d950a95490d3bb0516c44c08d08f65135d84525b069989583bbce05d7883558b0
    0x00000000015e24b21d385461b099fdba026a3b980b7358dd8ce779a057e8f57a59c913648bd10d3

private def aFastInv : ℕ → ℕ :=
  chunkLookupNat
    0x064e2d10b191048086b7132a1210ec1c49860794c813100da8873d828125137015761d0ac24acb8
    0x2fcbc4368081506c66b11781f8824129036518c7ea4332616af7181ac34a30880552b3618f940e4
    0x17cceab570497c9e60324f8556b0a0d4f22d3ce2629221518ede41bc442b7452586c07428e09a26
    0x39c8eef7b2e590147182008ff3ec2c781c342e82640613a54a27120e4ca4f6b80894971a4113a95
    0x1c8a6d319304b879430a9d8eb87385da745783cb6b21b8bc44e565bedb4482e8e91e737ea119ccc
    0x1042ec658895b66d25be14ead812c1cc466fba20cfe1a9fcfc0605831e9056e8b8a47588a35a4fc
    0x00200596a9ddb1070c1d8661b782aa023d18be91c88879c0f0b4850b1186977225c09328421eac5
    0x0000000003e6249c4928856ea3d2f56c6f06b64c24e16a6d9e8b2c0408a914f930465730269c4ac

private def bFastFun : ℕ → ℕ :=
  chunkLookupNat
    0x3c0c427683d480c66187c12f1830317afb41205c6de0794c68e46fa11222e2593156047588194cb
    0x28e090144409b29e34ab834131d02c510087a60028056865621c0abb588735b4395e75253ea18c5
    0x3c94c66159c864a46a234ee5e7e19190aa1d88ce82f41c1d27110005cbee107060a903580b17905
    0x440e0030dbb0929a6db5cb267199fd20ce51284a2a91bbb89002732b14add4507626602b9ad1841
    0x369e6655d8a8fa1644848b908692dc5a582ab44f8054d910f0d8738d52a7e26be462cd59bde1ae5
    0x30478be3ca50287a06938dcc72b280ec42470fc4c384b820e29c493a9989d2d2e9688f1c949febf
    0x3d0c6d303089de4f3d8d94ee821c499e6c7c2a022e2851a1641023ba5fad637a593e3d28079c109
    0x00000000016d723045a1c4a6d1242d92451081daa4642b007cdc4ca19fc0a2eae052b5353d98461

private def bFastInv : ℕ → ℕ :=
  chunkLookupNat
    0x3c210020d350de2f440f0624c282a05ccc1da99c6de0793594161cbf432bd83bc53804449d46851
    0x42534e9619a43ac181359a0591d2c97e78762581a8031a462256042849065553e870206043a1858
    0x381026656171e6217a9b49e5e7e29626b641280d8c64f92c1cb13d355dcc9498180e26431d9bb05
    0x440e0a72143dff04051542612199fd28a94ebb596ce4c97d88272b8acc8bc45365910d731adf03e
    0x0f4647302968f2e47599ce462229f0f6c56b8fd6ebb4da1600355f3612acd29ae8127e59b08c06a
    0x2783ee73ea41700000c28b6c70e08c581b7b34606af678548eab5ac49f6a2153e5688f6f8c09228
    0x3d15a680c089de7716a1c06b96e3a92e744603022e22734c161038c0508ae2026106da83185e4a3
    0x0000000001b9d052458d8528d1242dc2d2521502e462212882431bac1fcdb2e8504a9272a39ee1e

private def aFast : Equiv.Perm (Fin 276) :=
  let hf : ∀ i : Fin 276, aFastFun i.val < 276 := by decide +kernel
  let hg : ∀ i : Fin 276, aFastInv i.val < 276 := by decide +kernel
  let hfg : ∀ i : Fin 276, aFastInv (aFastFun i.val) = i.val := by decide +kernel
  let hgf : ∀ i : Fin 276, aFastFun (aFastInv i.val) = i.val := by decide +kernel
  { toFun := fun i ↦ ⟨aFastFun i.val, hf i⟩
    invFun := fun i ↦ ⟨aFastInv i.val, hg i⟩
    left_inv := fun i ↦ Fin.ext (hfg i)
    right_inv := fun i ↦ Fin.ext (hgf i) }

private def bFast : Equiv.Perm (Fin 276) :=
  let hf : ∀ i : Fin 276, bFastFun i.val < 276 := by decide +kernel
  let hg : ∀ i : Fin 276, bFastInv i.val < 276 := by decide +kernel
  let hfg : ∀ i : Fin 276, bFastInv (bFastFun i.val) = i.val := by decide +kernel
  let hgf : ∀ i : Fin 276, bFastFun (bFastInv i.val) = i.val := by decide +kernel
  { toFun := fun i ↦ ⟨bFastFun i.val, hf i⟩
    invFun := fun i ↦ ⟨bFastInv i.val, hg i⟩
    left_inv := fun i ↦ Fin.ext (hfg i)
    right_inv := fun i ↦ Fin.ext (hgf i) }

private theorem aFast_eq : aFast = a := Equiv.ext (by decide +kernel)

private theorem bFast_eq : bFast = b := Equiv.ext (by decide +kernel)

/-! ### Involution images of Djoković's generators -/

private def imgA : Equiv.Perm (Fin 276) :=
  packedInvol
    0x071800d5d26c0e22682f1ce50543460408288dc227e53b2c404c72b6d98140e81a14eb4aae05c3c
    0x1e452433e0c4f03f5017800886b124e4121b3b9224619105888f00b4d922b69110c4693719528fb
    0x2fcce8d12c0cc62863bd1843d883b53ee95aaf8aef079150e248098609ebb618314ce01c9490433
    0x22ce0b41dbe9d10f422948e6f401b4210121421444520399c2976c3b07053452044c7f7bbd4d427
    0x3bd5b0488aa554170792d06d7519e9903e2dbc5f2b10f26932f63aa5806244924c690c17a38cd12
    0x05836bd67378120e628b1426159b28604d2fb5442682c33c344e0fae404dd5b16512c6592716113
    0x181e6554f1595c352e1cc08df2d218327705b91c6d43b129d4cd5bc24150b6c9d1483a60b885a2a
    0x0000000002bd18ab2ea161cfe483680adc3dc020d05561902a7d83be21afd7e08d0e9d7f9b1306b
    (by decide +kernel) (by decide +kernel)

private def imgB : Equiv.Perm (Fin 276) :=
  packedInvol
    0x1a470bd183883a176a2493c650e1cd2c7e5e3085c8c6ebae209805a2c13121b3a1866b30b70029c
    0x114d4ea3e105a23f4043450c970158425a039f468841918c3eb608a74dcd8150a478a8444019cad
    0x135a4ed0c2e862b101bf9d2f467b5cf43763c24ae396b3e890a549c1d52f9343e164f26294e2246
    0x028e0b71321d0cb9199c610811f3002835212acb69a7643144e33a058da83452c058724c8108822
    0x2bc46ee3daa89e275a298a48d609da26a0708645a00681e4d80c4b8556a94288691cb347a454810
    0x101365d1239e0af5780edde597312606050928cff0a5c08026d3322157c8917a554e9025988deae
    0x179e64a6f32990ac331e01c432f8199ac672394ea1e4f8e9bef107809b70b6c8acb8556a86d7667
    0x000000000284104706c3e1c3d3bb697e58411420ccc80b12050412bd8c0fd7e3eca84e263ddfecb
    (by decide +kernel) (by decide +kernel)

private def imgC : Equiv.Perm (Fin 276) :=
  packedInvol
    0x0880a741c248661c4aaf0330f0aa502ef153c41350928909b00c32828129e2313c42eb683fdd2c9
    0x2f5cc43072818cb0189785848323043e5d7e8d58a1d7e0f9e4a62d34c78e37b9dd4adf37395a223
    0x1b4ce9f058e8c6836ebd12e3d1b9d91a2e5a96164f0621509c8807a140c53701311ec36a8edae07
    0x22ce0d42921e185087189486f402fdb87d65ab990cf598a4b8c2102a974bb452044c68693d59cea
    0x1ee0b04579cdd902098bc50824728544413302162f94984532cd2fa5836164d87994e825a8cb68c
    0x090067935261987c48800f4b7200d0aa4a3a8e6147f5f1143471392e5f0c783165c4782ba747eab
    0x181e6300a15a10ee70aa4086900a41ce4412b9056b4769344ef6309f9b70d6c8348f0324a245a6c
    0x00000000044625130906108da433f9801077c1d6cad5635951018000a1636193edf49c5c0a9bc6b
    (by decide +kernel) (by decide +kernel)

private def imgD : Equiv.Perm (Fin 276) :=
  packedInvol
    0x080b22233359be0d25445bc58881ccea563db0960493d1ac380c6a92c12f07501a14eb36c01023c
    0x11888363e250f10e548b000f44d9f98e5f21c3068796c891da2f37b4c7a2b150a538cf7f370626c
    0x134ce1f84a919cb1392206ec954311bae910860ae14711514a48842f900f934130141b081492445
    0x2c8e0e13021d0c854d1c5260127a5472772104c1e33201f568153a058c283450ba1a0311838d4bd
    0x28532b35e2807c5d5136ca6647229d5caa5bbc576281d2115a988138cfe414111d22ee47a3974c5
    0x3b1c02731b9d98f589179de3882230b8bf093956ac3281a5569d46ae60e9f5b300ecac459882313
    0x0ee0cd44f02190901834408072d3a19b0160a8d2c5544b403a192d8954d0b19362061e05bc85ad2
    0x0000000002bd941a0bc3c7e6e1ab680a6528ae1e7056335d2ee6013fc4cfd7e3ddf44e7c3edeccb
    (by decide +kernel) (by decide +kernel)

private def imgE : Equiv.Perm (Fin 276) :=
  packedInvol
    0x07060e91c06c8c220f2d57c6534c31d4ff6397456986eb2cb48c87829f6f819b39e46b49bc4e89c
    0x25d52963e105663f1f181624e340e43f10421f468077e0c4424b6c1b93a11152a8c4a869941d0cc
    0x0e8ce7b0c1b4c628288f57af409445de0d5e39e0c5685150907130894d43b704485ec32494dae1d
    0x22ce0b45da1d28e51b29548814040dec35211999075631ce2679009dd7452451bc5a64360109e17
    0x27e0b04768a488275ba3d068251a8544a0572e058006838d32102290d248601a5522d15323a100c
    0x24136c203424460e653e4f4133c315804a67b0588d60c97cb288393913ca75906912405b0f160e1
    0x179e605013c0b70155b99ea1510090b0ec42ae534d45793604dc07b79b70b6c8b88ebf6ab884cd2
    0x0000000001d8985c1b82dfafe0b368aacd46c00aead561fdbeee838521b0e19025f4c9043dcfceb
    (by decide +kernel) (by decide +kernel)

private def imgF : Equiv.Perm (Fin 276) :=
  packedInvol
    0x20dbc711ab5866a55f960b311491ed2e2439a9022e51dc10a68f3f3281294233f2267813a7154f1
    0x3a9b036383c1d6a337a853c0f4db54fad72187df41d67159b84c54b4d5c2b691d20003373b42823
    0x340a90c2e309b3077328a06c841195f2480c8696c317099c1ae9762ad5add700be24c36096a2007
    0x3ccf8e253a45f0984b088baa04caf4163845059e8df0231de5021484e0220210f84ccf3631a0a95
    0x0b09ecb280045c934423038121f9807a814e8f13e021d38d00850aa10d2085405d0e8d0623920a6
    0x420d06d1930198ac053bcbc7735b6e124a321259a1b5e1fd7cb7773f562bb2bb9da8f5832e1610a
    0x1e916760010592ba129448045293fd6a610843934892a934f221270c18ada319106e1e1cad05a2a
    0x000000000014961823bd9c8fe3342d5ec468989646a0717cea72143a21ab9033ec685b433de1eb3
    (by decide +kernel) (by decide +kernel)

private def imgG : Equiv.Perm (Fin 276) :=
  packedInvol
    0x301b8b5788b52ec4373a5da4881ac4662483b2c46e57a174b8b91932812b2753d8c0273c0e15435
    0x118d436453ccdadb403ca187a1d18c044721800541505959bc4c56879a8cc1a1d0ee045f9642811
    0x1a0a89e29acc72737601524dd070359311129490c315d99cca58732f152c8268be250d608606e45
    0x3c0849f8521cae984b33608a01f1a59c9c382e07675018a1427914989a2e73e2643640582a0887f
    0x2d05ca45f0049e6b57c3a12ac62c4cec8144999c47d4db8cde850ea117b066317d22ba7ea39dce4
    0x1c9a0eb3f20c56120516c9d0049a8c38fe7a924442655a54a05548030f6e17c0815c6404058d8a7
    0x03c823d0fa2df28d0c9859e070d3fce25108231349d5bb8204302f0847f0b6ac1620d36c8b1acfa
    0x000000000288965a6bbf14c4a1e36910a58084d28d84105dbf0863ba1868f87beda4ef5b3dc0cc2
    (by decide +kernel) (by decide +kernel)

private def imageAt : ℕ → Equiv.Perm (Fin 276)
  | 0 => imgA
  | 1 => imgB
  | 2 => imgC
  | 3 => imgD
  | 4 => imgE
  | 5 => imgF
  | _ => imgG

/-- The seven involutions in `Equiv.Perm (Fin 276)` assigned to the generators `a` through `g` of
Djoković's presentation of `Co₃`. -/
def presentationImage (i : Fin SporadicName.Co3.presentation.generatorCount) :
    Equiv.Perm (Fin 276) :=
  imageAt i.val

/-! ### Verification of the twenty-four relators -/

private theorem relator0 : imgA ^ 2 = 1 := packedInvol_sq _ _ _ _ _ _ _ _ _ _
private theorem relator1 : imgB ^ 2 = 1 := packedInvol_sq _ _ _ _ _ _ _ _ _ _
private theorem relator2 : imgC ^ 2 = 1 := packedInvol_sq _ _ _ _ _ _ _ _ _ _
private theorem relator3 : imgD ^ 2 = 1 := packedInvol_sq _ _ _ _ _ _ _ _ _ _
private theorem relator4 : imgE ^ 2 = 1 := packedInvol_sq _ _ _ _ _ _ _ _ _ _
private theorem relator5 : imgF ^ 2 = 1 := packedInvol_sq _ _ _ _ _ _ _ _ _ _
private theorem relator6 : imgG ^ 2 = 1 := packedInvol_sq _ _ _ _ _ _ _ _ _ _
private theorem relator7 : (imgA * imgC) ^ 2 = 1 := Equiv.ext (by decide +kernel)
private theorem relator8 : (imgA * imgD) ^ 2 = 1 := Equiv.ext (by decide +kernel)
private theorem relator9 : (imgA * imgE) ^ 2 = 1 := Equiv.ext (by decide +kernel)
private theorem relator10 : (imgB * imgD) ^ 2 = 1 := Equiv.ext (by decide +kernel)
private theorem relator11 : (imgC * imgE) ^ 2 = 1 := Equiv.ext (by decide +kernel)
private theorem relator12 : (imgD * imgG) ^ 2 = 1 := Equiv.ext (by decide +kernel)
private theorem relator13 : (imgE * imgG) ^ 2 = 1 := Equiv.ext (by decide +kernel)
private theorem relator14 : (imgA * imgB) ^ 3 = 1 := Equiv.ext (by decide +kernel)
private theorem relator15 : (imgC * imgD) ^ 3 = 1 := Equiv.ext (by decide +kernel)
private theorem relator16 : (imgD * imgE) ^ 3 = 1 := Equiv.ext (by decide +kernel)
private theorem relator17 : imgF * (imgA * imgG) ^ 3 = 1 := Equiv.ext (by decide +kernel)
private theorem relator18 : imgG * (imgB * imgF) ^ 3 = 1 := Equiv.ext (by decide +kernel)
private theorem relator19 : (imgC * imgF * imgG) ^ 3 = 1 := Equiv.ext (by decide +kernel)
private theorem relator20 : imgE * (imgA * imgB * imgC) ^ 3 = 1 := Equiv.ext (by decide +kernel)
private theorem relator21 : imgE * (imgA * imgC * imgG) ^ 4 = 1 := Equiv.ext (by decide +kernel)
private theorem relator22 : (imgB * imgC * imgF * imgC * imgF) ^ 3 = 1 :=
  Equiv.ext (by decide +kernel)
private theorem relator23 : imgE * (imgA * imgB * imgC * imgF) ^ 7 = 1 :=
  Equiv.ext (by decide +kernel)

/-- All twenty-four transcribed relators of `Co₃` hold at `presentationImage`. -/
theorem lift_presentationImage_toFreeGroup_eq_one :
    ∀ t ∈ SporadicName.Co3.presentation.transcribed,
      FreeGroup.lift presentationImage t.toFreeGroup = 1 := by
  -- Abstract the presentation first, because it occurs in the generator index type.
  suffices key : ∀ P : GroupPresentation, P = co3Presentation → ∀ t ∈ P.transcribed,
      FreeGroup.lift (fun i : Fin P.generatorCount ↦ imageAt i.val) t.toFreeGroup = 1 from
    key _ SporadicName.presentation_Co3
  rintro P rfl
  simp only [co3Presentation_transcribed, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Relator.lift_toFreeGroup, Relator.eval_mul, Relator.eval_pow,
    Relator.eval_gen, imageAt]
  exact ⟨relator0, relator1, relator2, relator3, relator4, relator5, relator6,
    relator7, relator8, relator9, relator10, relator11, relator12, relator13,
    relator14, relator15, relator16, relator17, relator18, relator19, relator20,
    relator21, relator22, relator23⟩

/-! ### Generation of the ATLAS model -/

private def wordStep : Fin 4 → Equiv.Perm (Fin 276)
  | 0 => aFast
  | 1 => aFast⁻¹
  | 2 => bFast
  | 3 => bFast⁻¹

private def stepNat : Fin 4 → ℕ → ℕ
  | 0 => aFastFun
  | 1 => aFastInv
  | 2 => bFastFun
  | 3 => bFastInv

private def wordFast (l : List (Fin 4)) : Equiv.Perm (Fin 276) :=
  (l.map wordStep).prod

private def evalWordNat (l : List (Fin 4)) (i : ℕ) : ℕ :=
  l.foldr stepNat i

private theorem wordFast_apply_val (l : List (Fin 4)) (i : Fin 276) :
    (wordFast l i).val = evalWordNat l i.val := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    have hstep : ∀ x : Fin 276, (wordStep t x).val = stepNat t x.val :=
      match t with
      | 0 | 1 | 2 | 3 => fun _ ↦ rfl
    simp only [wordFast, evalWordNat, List.map_cons, List.prod_cons, List.foldr_cons,
      Equiv.Perm.mul_apply, hstep]
    exact congrArg (stepNat t) ih

private theorem eq_wordFast (σ : Equiv.Perm (Fin 276)) (l : List (Fin 4))
    (h : ∀ i : Fin 276, (σ i).val = evalWordNat l i.val) : σ = wordFast l :=
  Equiv.ext fun i ↦ Fin.ext ((h i).trans (wordFast_apply_val l i).symm)

private theorem wordFast_mem (l : List (Fin 4)) : wordFast l ∈ Co3 := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hg
  match t with
  | 0 => dsimp [wordStep]; rw [aFast_eq]; exact a_mem
  | 1 => dsimp [wordStep]; rw [aFast_eq]; exact inv_mem a_mem
  | 2 => dsimp [wordStep]; rw [bFast_eq]; exact b_mem
  | 3 => dsimp [wordStep]; rw [bFast_eq]; exact inv_mem b_mem

private theorem imgA_eq :
    imgA = wordFast
    [0, 3, 1, 2, 1, 2, 0, 2, 1, 2, 2, 0, 2, 1, 3, 0, 3, 1, 2, 0, 2, 2, 1, 3, 1,
     2, 0, 3, 0, 3, 3, 1, 2, 1, 3, 1, 3, 3, 0, 2, 1, 2, 1, 3, 1, 3, 0, 2, 2, 1,
     2, 0, 3, 1, 2, 0, 3, 0, 3, 0, 3, 1, 2, 0, 3, 1, 2, 0, 2, 1, 3, 1] :=
  eq_wordFast _ _ (by decide +kernel)

private theorem imgB_eq :
    imgB = wordFast
    [3, 3, 1, 3, 0, 3, 3, 0, 3, 1, 3, 3, 0, 2, 1, 3, 1, 2, 0, 2, 0, 2, 0, 3, 3,
     1, 3, 3, 0, 2, 2, 1, 3, 0, 3, 1, 2, 0, 3, 3, 1, 3, 0, 3, 3, 1, 2, 1, 3, 0,
     3, 1, 3, 0, 3, 0, 2, 0, 2, 0] :=
  eq_wordFast _ _ (by decide +kernel)

private theorem imgC_eq :
    imgC = wordFast
    [1, 2, 0, 2, 1, 3, 1, 3, 3, 0, 2, 2, 0, 2, 2, 1, 2, 0, 2, 2, 0, 3, 1, 3, 0,
     3, 3, 1, 3, 0, 3, 3, 1, 2, 1, 3, 0, 3, 1, 3, 0, 3, 0, 2, 0, 2, 2, 0, 3, 1,
     3, 3, 0, 2, 0, 3, 3, 1, 3, 1, 2, 2, 0, 2, 1, 3, 0] :=
  eq_wordFast _ _ (by decide +kernel)

private theorem imgD_eq :
    imgD = wordFast
    [3, 1, 3, 1, 3, 0, 2, 2, 1, 2, 1, 3, 0, 3, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 3,
     1, 3, 1, 3, 3, 0, 2, 0, 2, 2, 0, 3, 0, 2, 2, 0, 2, 0, 3, 0, 3, 0, 3, 1, 3,
     3, 0, 2, 1, 2, 1, 2, 0, 3, 1, 2, 0, 3, 0, 3, 3, 1, 2, 1, 3, 0, 2, 0, 3] :=
  eq_wordFast _ _ (by decide +kernel)

private theorem imgG_eq :
    imgG = wordFast
    [1, 3, 1, 3, 0, 2, 1, 3, 0, 2, 1, 3, 1, 2, 0, 2, 0, 2, 1, 2, 0, 3, 0, 3, 0,
     3, 1, 2, 0, 3, 1, 2, 0, 2, 1, 3, 1, 2, 0, 2, 0, 3, 1, 3, 1, 3, 0, 2, 1, 2,
     1, 2, 1, 2, 1, 2, 1, 2, 0, 3, 0, 3, 1, 3, 0, 3, 1, 3, 0, 2, 2, 0] :=
  eq_wordFast _ _ (by decide +kernel)

private theorem imgA_mem : imgA ∈ Co3 := imgA_eq ▸ wordFast_mem _
private theorem imgB_mem : imgB ∈ Co3 := imgB_eq ▸ wordFast_mem _
private theorem imgC_mem : imgC ∈ Co3 := imgC_eq ▸ wordFast_mem _
private theorem imgD_mem : imgD ∈ Co3 := imgD_eq ▸ wordFast_mem _
private theorem imgG_mem : imgG ∈ Co3 := imgG_eq ▸ wordFast_mem _

private theorem imgF_mem : imgF ∈ Co3 := by
  rw [eq_inv_of_mul_eq_one_left relator17]
  exact inv_mem (pow_mem (mul_mem imgA_mem imgG_mem) 3)

private theorem imgE_mem : imgE ∈ Co3 := by
  rw [eq_inv_of_mul_eq_one_left relator20]
  exact inv_mem (pow_mem (mul_mem (mul_mem imgA_mem imgB_mem) imgC_mem) 3)

/-- Every generator image lies in the ATLAS model `Co3`. -/
theorem presentationImage_mem (i : Fin SporadicName.Co3.presentation.generatorCount) :
    presentationImage i ∈ Co3 := by
  have hi : i.val < 7 := by simpa using i.isLt
  rw [presentationImage]
  interval_cases i.val
  · exact imgA_mem
  · exact imgB_mem
  · exact imgC_mem
  · exact imgD_mem
  · exact imgE_mem
  · exact imgF_mem
  · exact imgG_mem

/-- Every generator image has order two. -/
theorem orderOf_presentationImage (i : Fin SporadicName.Co3.presentation.generatorCount) :
    orderOf (presentationImage i) = 2 := by
  have hi : i.val < 7 := by simpa using i.isLt
  rw [presentationImage]
  interval_cases i.val
  · exact orderOf_eq_prime relator0 (by decide +kernel)
  · exact orderOf_eq_prime relator1 (by decide +kernel)
  · exact orderOf_eq_prime relator2 (by decide +kernel)
  · exact orderOf_eq_prime relator3 (by decide +kernel)
  · exact orderOf_eq_prime relator4 (by decide +kernel)
  · exact orderOf_eq_prime relator5 (by decide +kernel)
  · exact orderOf_eq_prime relator6 (by decide +kernel)

private theorem a_eq_recovery : a = (imgF * imgC * imgG * imgC * imgD) ^ 3 := by
  rw [← aFast_eq]
  exact Equiv.ext (by decide +kernel)

private theorem b_eq_recovery : b = (imgC * imgF * imgD * imgB * imgG * imgA) ^ 3 := by
  rw [← bFast_eq]
  exact Equiv.ext (by decide +kernel)

/-- The seven presentation images generate exactly the ATLAS model `Co3`. -/
theorem closure_range_presentationImage :
    Subgroup.closure (Set.range presentationImage) = Co3 := by
  have hcount : SporadicName.Co3.presentation.generatorCount = 7 := by simp
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact presentationImage_mem i
  · rw [Co3_def, Subgroup.closure_le]
    have hmem : ∀ k < 7, imageAt k ∈ Subgroup.closure (Set.range presentationImage) :=
      fun k hk ↦ Subgroup.subset_closure ⟨⟨k, hcount.symm ▸ hk⟩, rfl⟩
    have hA : imgA ∈ Subgroup.closure (Set.range presentationImage) := hmem 0 (by decide)
    have hB : imgB ∈ Subgroup.closure (Set.range presentationImage) := hmem 1 (by decide)
    have hC : imgC ∈ Subgroup.closure (Set.range presentationImage) := hmem 2 (by decide)
    have hD : imgD ∈ Subgroup.closure (Set.range presentationImage) := hmem 3 (by decide)
    have hF : imgF ∈ Subgroup.closure (Set.range presentationImage) := hmem 5 (by decide)
    have hG : imgG ∈ Subgroup.closure (Set.range presentationImage) := hmem 6 (by decide)
    rintro σ (rfl | rfl)
    · rw [SetLike.mem_coe, a_eq_recovery]
      exact pow_mem (mul_mem (mul_mem (mul_mem (mul_mem hF hC) hG) hC) hD) 3
    · rw [SetLike.mem_coe, b_eq_recovery]
      exact pow_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hC hF) hD) hB) hG) hA) 3

/-! ### The homomorphism from the presented group -/

/-- The homomorphism from the presented third Conway group into `Equiv.Perm (Fin 276)` extending
`presentationImage`. -/
def presentationHom : SporadicName.Co3.Group →* Equiv.Perm (Fin 276) :=
  SporadicName.Co3.presentation.homEquiv.symm
    ⟨presentationImage, lift_presentationImage_toFreeGroup_eq_one⟩

/-- `presentationHom` is the lift of `presentationImage` through
`TauCeti.GroupPresentation.homEquiv`. -/
theorem presentationHom_def :
    presentationHom = SporadicName.Co3.presentation.homEquiv.symm
      ⟨presentationImage, lift_presentationImage_toFreeGroup_eq_one⟩ :=
  (rfl)

/-- `presentationHom` sends each presentation generator to its assigned involution. -/
@[simp]
theorem presentationHom_of (i : Fin SporadicName.Co3.presentation.generatorCount) :
    presentationHom (PresentedGroup.of i) = presentationImage i :=
  GroupPresentation.homEquiv_symm_apply_of _ _ i

/-- The range of `presentationHom` is the ATLAS model `Co3`. -/
@[simp]
theorem range_presentationHom : presentationHom.range = Co3 :=
  (GroupPresentation.range_homEquiv_symm _ _).trans closure_range_presentationImage

end Co3

/-- The presented third Conway group maps surjectively onto its ATLAS degree-276 permutation
model. -/
theorem exists_surjective_Co3 :
    ∃ f : SporadicName.Co3.Group →* Co3, Function.Surjective f :=
  SporadicName.Co3.presentation.exists_surjective_of_closure_range_eq
    ⟨Co3.presentationImage, Co3.lift_presentationImage_toFreeGroup_eq_one⟩
    Co3.closure_range_presentationImage

/-- The presented third Conway group is nontrivial. -/
instance : Nontrivial SporadicName.Co3.Group :=
  exists_surjective_Co3.choose_spec.nontrivial

end TauCeti.Sporadic
