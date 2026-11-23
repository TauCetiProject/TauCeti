/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA.Composition
public import TauCeti.LowDimTopology.Bordered.TypeA.Homotopy

/-!
# Homotopy invariance of the box tensor product in the type `A` module

A morphism `f` of `A∞` modules from `M` to `M'` induces the chain map
`T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` of box tensor products with a type `D` structure
`N` (`TauCeti.TypeDStructure.typeABoxMapOfHom`), and a homotopy `H` between morphisms induces a
chain homotopy `T_H` (`TauCeti.TypeDStructure.typeABoxHomotopy`). For a homotopy `H` between
`g ∘ f` and the identity, this file proves the identity `T_g ∘ T_f + id = ∂ ∘ T_H + T_H ∘ ∂` on
row vectors under either boundedness hypothesis. It also shows that, for strictly unital modules,
morphisms and homotopies and idempotents that are cycles, `T_f` and `T_H` restrict to the box
tensor products `M ⊗ N` over the ring of idempotents.

* **Homotopy invariance.** Let `f : M → M'` and `g : M' → M` be morphisms with a homotopy `H`
  between `g ∘ f` and the identity of `M`. Then on row vectors

  `T_g ∘ T_f + id = ∂ ∘ T_H + T_H ∘ ∂`,

  when `N` is bounded (`TauCeti.TypeDStructure.typeABoxMapOfHom_typeABoxMapOfHom_add_of_isBounded`)
  or the modules, the morphisms and the homotopy are
  (`TauCeti.TypeDStructure.typeABoxMapOfHom_typeABoxMapOfHom_add_of_act_eq_zero`). This combines
  the three facts `T_{g ∘ f} = T_g ∘ T_f` (`TauCeti.LowDimTopology.Bordered.TypeA.Composition`),
  `T_{id} = id`, and `T_{g ∘ f} + T_{id} = ∂ ∘ T_H + T_H ∘ ∂`
  (`TauCeti.LowDimTopology.Bordered.TypeA.Homotopy`). Together with the same identity for a
  homotopy between `f ∘ g` and the identity of `M'`, which is not stated separately here, one
  obtains that a homotopy equivalence of type `A` modules induces a homotopy equivalence of the
  complexes of row vectors.
* **The box tensor product over the idempotents.** The box tensor product of a strictly unital
  module `M` is the submodule `M ⊗ N` of row vectors fixed by the idempotents
  (`TauCeti.TypeDStructure.typeABoxTensor`). When the idempotents are cycles, the maps `T_f` and
  homotopies `T_H` induced by strictly unital morphisms and homotopies
  (`TauCeti.UngradedAInfinityRightModuleHom.IsStrictlyUnital`), as in bordered Floer theory, map
  `M ⊗ N` into `M' ⊗ N` (`TauCeti.TypeDStructure.typeABoxMapOfHom_mem_typeABoxTensor`,
  `TauCeti.TypeDStructure.typeABoxHomotopy_mem_typeABoxTensor`). Here `T_f` is the `M'`-component
  of the box tensor differential of the mapping cone of `f`, a strictly unital module
  (`TauCeti.UngradedAInfinityRightModuleHom.IsStrictlyUnital.cone`). A homotopy between `g ∘ f` and
  the identity qualifies when `f`, `g` and the homotopy are strictly unital, by
  `TauCeti.UngradedAInfinityRightModuleHom.IsStrictlyUnital.comp` and
  `TauCeti.UngradedAInfinityRightModuleHom.isStrictlyUnital_id`. As an informal remark: restricting
  the identity above to these submodules, and combining it with the invariance in the type `D`
  structure (`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_of_act_eq_zero`), one obtains
  that the box tensor product over the idempotents is invariant under homotopy equivalences of
  both factors; this file does not state that consequence as a theorem.

## Main results

* `TauCeti.TypeDStructure.typeABoxMapOfHom_mem_typeABoxTensor`: a strictly unital morphism of
  strictly unital modules induces a map `M ⊗ N → M' ⊗ N`.
* `TauCeti.TypeDStructure.typeABoxHomotopy_mem_typeABoxTensor`: a strictly unital homotopy between
  strictly unital morphisms induces a map `M ⊗ N → M' ⊗ N`.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_typeABoxMapOfHom_add_of_isBounded` and
  `TauCeti.TypeDStructure.typeABoxMapOfHom_typeABoxMapOfHom_add_of_act_eq_zero`: homotopy
  invariance of the box tensor product in the type `A` module, `T_g ∘ T_f + id = ∂ T_H + T_H ∂`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (strictly unital `A∞` modules and morphisms over `𝔽₂`, and the invariance of the box
  tensor product under homotopy equivalences).
-/

public section

namespace TauCeti

namespace TypeDStructure

variable {R A M M' : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*}
  [Fintype X] [DecidableEq X] {N : TypeDStructure d ι X} {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'}

/-! ### The box tensor product over the idempotents -/

omit [DecidableEq X] in
/-- A row vector `x ↦ (φ x, 0)` of the mapping cone of a strictly unital morphism is fixed by the
idempotents when `φ` is: the cone acts on it by `(m₂(φ x, ι s), f₂(φ x, ι s)) = (φ x, 0)`. -/
private theorem mk_zero_mem_typeABoxTensor_cone {f : UngradedAInfinityRightModuleHom Mm Mm'}
    (hf : f.IsStrictlyUnital ι) {φ : X → M} (hφ : φ ∈ N.typeABoxTensor Mm) :
    (fun x => (φ x, 0)) ∈ N.typeABoxTensor f.cone := mem_typeABoxTensor_iff.2 fun x => by
  rw [UngradedAInfinityRightModuleHom.cone_act_apply, hf.map_eq_zero (i := 0) rfl,
    mem_typeABoxTensor_iff.1 hφ x]
  simp

omit [DecidableEq X] in
/-- The second components of a row vector of the mapping cone of a strictly unital morphism fixed
by the idempotents are fixed by the idempotents: the cone acts on second components by `m'₂`,
since `f₂(·, ι s) = 0`. -/
private theorem snd_mem_typeABoxTensor_cone {f : UngradedAInfinityRightModuleHom Mm Mm'}
    (hf : f.IsStrictlyUnital ι) {ψ : X → M × M'} (hψ : ψ ∈ N.typeABoxTensor f.cone) :
    (fun x => (ψ x).2) ∈ N.typeABoxTensor Mm' := mem_typeABoxTensor_iff.2 fun x => by
  have h := congrArg Prod.snd (mem_typeABoxTensor_iff.1 hψ x)
  rwa [UngradedAInfinityRightModuleHom.cone_act_apply, hf.map_eq_zero (i := 0) rfl,
    LinearMap.zero_apply, add_zero] at h

/-- **A strictly unital morphism induces a map of box tensor products over the idempotents.**
Over a ring of characteristic two, let `M` and `M'` be strictly unital, the idempotents cycles,
and `f` a strictly unital morphism. Then `T_f` maps `M ⊗ N` into `M' ⊗ N`. -/
theorem typeABoxMapOfHom_mem_typeABoxTensor [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    (hMm' : Mm'.IsStrictlyUnital ι) (hι : ∀ s, d (ι s) = 0)
    {f : UngradedAInfinityRightModuleHom Mm Mm'} (hf : f.IsStrictlyUnital ι) {φ : X → M}
    (hφ : φ ∈ N.typeABoxTensor Mm) : N.typeABoxMapOfHom f φ ∈ N.typeABoxTensor Mm' :=
  mem_typeABoxTensor_iff.2 fun z => by
    rw [typeABoxMapOfHom_apply]
    exact mem_typeABoxTensor_iff.1 (snd_mem_typeABoxTensor_cone hf
      (typeABoxDifferential_mem_typeABoxTensor (hf.cone hMm hMm') hι
        (mk_zero_mem_typeABoxTensor_cone hf hφ))) z

/-- **A strictly unital homotopy induces a map of box tensor products over the idempotents.**
Over a ring of characteristic two, let `M` and `M'` be strictly unital, the idempotents cycles,
and `H` a strictly unital homotopy between strictly unital morphisms `f` and `g`. Then `T_H` maps
`M ⊗ N` into `M' ⊗ N`. -/
theorem typeABoxHomotopy_mem_typeABoxTensor [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    (hMm' : Mm'.IsStrictlyUnital ι) (hι : ∀ s, d (ι s) = 0)
    {f g : UngradedAInfinityRightModuleHom Mm Mm'} (hf : f.IsStrictlyUnital ι)
    (hg : g.IsStrictlyUnital ι) {H : UngradedAInfinityRightModuleHom.Homotopy f g}
    (hH : H.IsStrictlyUnital ι) {φ : X → M} (hφ : φ ∈ N.typeABoxTensor Mm) :
    N.typeABoxHomotopy H φ ∈ N.typeABoxTensor Mm' :=
  mem_typeABoxTensor_iff.2 fun z => by
    rw [typeABoxHomotopy_apply]
    -- `T_H` is the `M'`-component of the map induced by `(id, h)` into the cone of `f + g`.
    exact mem_typeABoxTensor_iff.1 (snd_mem_typeABoxTensor_cone (hf.add hg)
      (typeABoxMapOfHom_mem_typeABoxTensor hMm ((hf.add hg).cone hMm hMm') hι hH.toConeHom hφ)) z

/-! ### Homotopy invariance -/

/-- **Homotopy invariance of the box tensor product with a bounded type `D` structure, in the type
`A` module.** Over a ring of characteristic two, let the iterates `δⁿ` of `N` vanish for all
large `n`, and let `H` be a homotopy between the composite of morphisms `f : M → M'` and
`g : M' → M` and the identity of `M`. Then `T_g ∘ T_f + id = ∂ ∘ T_H + T_H ∘ ∂` on row vectors.
For strictly unital modules, morphisms and homotopies and idempotents that are cycles, the maps
involved restrict to the box tensor products over the idempotents; see
`TauCeti.TypeDStructure.typeABoxMapOfHom_mem_typeABoxTensor` and
`TauCeti.TypeDStructure.typeABoxHomotopy_mem_typeABoxTensor`. -/
theorem typeABoxMapOfHom_typeABoxMapOfHom_add_of_isBounded [CharP R 2]
    (N : TypeDStructure d ι X) (hN : N.IsBounded) {f : UngradedAInfinityRightModuleHom Mm Mm'}
    {g : UngradedAInfinityRightModuleHom Mm' Mm}
    (H : UngradedAInfinityRightModuleHom.Homotopy (g.comp f)
      (UngradedAInfinityRightModuleHom.id Mm)) (φ : X → M) :
    N.typeABoxMapOfHom g (N.typeABoxMapOfHom f φ) + φ =
      N.typeABoxDifferential Mm (N.typeABoxHomotopy H φ) +
        N.typeABoxHomotopy H (N.typeABoxDifferential Mm φ) := by
  have h := N.typeABoxMapOfHom_add_typeABoxMapOfHom_of_isBounded hN H φ
  rwa [N.typeABoxMapOfHom_comp_of_isBounded g f hN, N.typeABoxMapOfHom_id_of_isBounded hN,
    LinearMap.comp_apply, LinearMap.id_apply] at h

/-- **Homotopy invariance of the box tensor product of bounded type `A` modules.** Over a ring of
characteristic two, let the operations of `M` and `M'`, the components of morphisms
`f : M → M'` and `g : M' → M`, and those of a homotopy `H` between `g ∘ f` and the identity of
`M` vanish from arity `K` on. Then `T_g ∘ T_f + id = ∂ ∘ T_H + T_H ∘ ∂` on row vectors, whatever
the type `D` structure; see
`TauCeti.TypeDStructure.typeABoxMapOfHom_typeABoxMapOfHom_add_of_isBounded`. -/
theorem typeABoxMapOfHom_typeABoxMapOfHom_add_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) {f : UngradedAInfinityRightModuleHom Mm Mm'}
    {g : UngradedAInfinityRightModuleHom Mm' Mm}
    (H : UngradedAInfinityRightModuleHom.Homotopy (g.comp f)
      (UngradedAInfinityRightModuleHom.id Mm)) {K : ℕ} (hM : ∀ n, K ≤ n → Mm.act n = 0)
    (hM' : ∀ n, K ≤ n → Mm'.act n = 0) (hf : ∀ n, K ≤ n → f.map n = 0)
    (hg : ∀ n, K ≤ n → g.map n = 0) (hH : ∀ n, K ≤ n → H.map n = 0) (φ : X → M) :
    N.typeABoxMapOfHom g (N.typeABoxMapOfHom f φ) + φ =
      N.typeABoxDifferential Mm (N.typeABoxHomotopy H φ) +
        N.typeABoxHomotopy H (N.typeABoxDifferential Mm φ) := by
  -- The components of `g ∘ f` vanish from arity `K + K` on, and those of the identity from `1`.
  have h := N.typeABoxMapOfHom_add_typeABoxMapOfHom_of_act_eq_zero H (K := K + K + 1)
    (fun n hn => hM n (by omega)) (fun n hn => hM n (by omega))
    (fun n hn => g.comp_map_eq_zero f hf hg (by omega))
    (fun n hn => UngradedAInfinityRightModuleHom.id_map_eq_zero (by omega))
    (fun n hn => hH n (by omega)) φ
  rwa [N.typeABoxMapOfHom_comp_of_act_eq_zero g f hM hM' hM hf hg,
    N.typeABoxMapOfHom_id_of_act_eq_zero hM, LinearMap.comp_apply, LinearMap.id_apply] at h

end TypeDStructure

end TauCeti
