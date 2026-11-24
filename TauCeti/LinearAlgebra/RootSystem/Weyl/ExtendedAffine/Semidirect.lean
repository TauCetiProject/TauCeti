/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Alcove

/-!
# The extended affine Weyl group as a semidirect product, and intermediate lattices

Let `P` be a root pairing with coweight space `N`, Weyl group `W` (acting on `N` through the
coreflections), coroot lattice `Q∨ = P.corootSpan ℤ` and coweight lattice
`P∨ = P.coweightLattice`. For a lattice `Y` with `Q∨ ⊆ Y ⊆ P∨`, the group

`W_Y = Y ⋊ W`

of affine automorphisms of `N` (`RootPairing.latticeAffineWeylGroup`, in
`TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Basic`) lies between the affine Weyl group
`W_aff` and the extended affine Weyl group `W_ext`, and the class of the translation part modulo
`Q∨` is a homomorphism `W_Y → Y / Q∨` with kernel `W_aff`
(`RootPairing.ker_latticeAffineWeylGroupToQuotient`).

Let `b` be a base of a finite, reduced, irreducible, crystallographic pairing over a linearly
ordered field, `A` its fundamental alcove and `Ω = Stab_{W_ext}(A)`. The stabilizer of `A` in `W_Y`
is `Ω_Y = Ω ∩ W_Y` (`RootPairing.latticeFundamentalAlcoveStabilizer`), the elements of `Ω` whose
translation part lies in `Y`; this definition and its elementary API only need a commutative ring
with a preorder, like `Ω` itself. Since `W_aff` acts freely on the alcoves it meets `Ω_Y`
trivially, and over an archimedean field it is transitive on the alcoves, so `W_Y = W_aff ⊔ Ω_Y`.
As `W_ext` normalizes `W_aff`, multiplication is therefore an isomorphism

`W_aff ⋊ Ω_Y ≃* W_Y`

(`RootPairing.latticeAffineWeylGroupMulEquiv`), and `Ω_Y ≃* Y / Q∨` through the class of the
translation part (`RootPairing.latticeFundamentalAlcoveStabilizerEquivQuotient`). The inverse of
the semidirect-product isomorphism takes `f` to the pair `(f ω⁻¹, ω)`, where `ω` is the unique
element of `Ω_Y` whose translation part is congruent to that of `f` modulo `Q∨`
(`RootPairing.latticeAffineWeylGroupMulEquiv_symm_apply_right`). The case `Y = P∨` is the classical
decomposition `W_ext ≃* W_aff ⋊ Ω` (`RootPairing.extendedAffineWeylGroupMulEquiv`). For `Y = Q∨` the
group `Ω_Y` is trivial, and for `Y = P∨` it is `Ω`.

## Main definitions

* `RootPairing.latticeFundamentalAlcoveStabilizer`: the stabilizer `Ω_Y` of the fundamental alcove
  in `W_Y`.
* `RootPairing.latticeFundamentalAlcoveStabilizerEquivQuotient`: **the isomorphism
  `Ω_Y ≃* Y / Q∨`.**
* `RootPairing.latticeAffineWeylGroupMulEquiv`: **the isomorphism `W_aff ⋊ Ω_Y ≃* W_Y`.**
* `RootPairing.extendedAffineWeylGroupMulEquiv`: **the isomorphism `W_aff ⋊ Ω ≃* W_ext`.**

## Main results

* `RootPairing.mem_latticeFundamentalAlcoveStabilizer`: membership in `Ω_Y`.
* `RootPairing.affineWeylGroup_inf_fundamentalAlcoveStabilizer` and
  `RootPairing.affineWeylGroup_inf_latticeFundamentalAlcoveStabilizer`: `W_aff ∩ Ω` and
  `W_aff ∩ Ω_Y` are trivial.
* `RootPairing.affineWeylGroup_sup_latticeFundamentalAlcoveStabilizer`: `W_aff ⊔ Ω_Y = W_Y`.
* `RootPairing.latticeFundamentalAlcoveStabilizer_corootSpan` and
  `RootPairing.latticeFundamentalAlcoveStabilizer_coweightLattice`: `Ω_{Q∨} = 1` and `Ω_{P∨} = Ω`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §2.3 (the group `Ω` and the
  decomposition of the extended affine Weyl group as `W_a ⋊ Ω`).
* A. Garnier, *Fundamental domains for extended affine Weyl groups*, 2020, Proposition 2.3.1
  (the decomposition `W_Y = W_aff ⋊ Ω_Y` for an intermediate lattice `Y`).
-/

public section

open Set Function

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} (b : P.Base) [CharZero R] [Preorder R]
  [Finite ι] [Nonempty ι]

/-! ### The stabilizer `Ω_Y` of the fundamental alcove in `W_Y` -/

section Lattice

variable {Y : Submodule ℤ N} (hQ : P.corootSpan ℤ ≤ Y) (hP : Y ≤ P.coweightLattice)

variable (P Y) in
/-- The **stabilizer `Ω_Y` of the fundamental alcove** in the group `W_Y = Y ⋊ W` of a lattice
`Q∨ ⊆ Y ⊆ P∨`: the elements of `W_Y` stabilizing the fundamental alcove of the base `b`, that is,
`Ω ∩ W_Y`. -/
def latticeFundamentalAlcoveStabilizer : Subgroup (N ≃ᵃ[R] N) :=
  P.fundamentalAlcoveStabilizer b ⊓ P.latticeAffineWeylGroup Y hQ hP

/-- An element lies in `Ω_Y` exactly when it lies in `Ω` and its translation part lies in `Y`. -/
@[simp]
theorem mem_latticeFundamentalAlcoveStabilizer {f : N ≃ᵃ[R] N} :
    f ∈ P.latticeFundamentalAlcoveStabilizer b Y hQ hP ↔
      f ∈ P.fundamentalAlcoveStabilizer b ∧ f 0 ∈ Y := by
  rw [latticeFundamentalAlcoveStabilizer, Subgroup.mem_inf, P.mem_latticeAffineWeylGroup_iff]
  exact and_congr_right fun hf ↦ and_iff_right
    (P.mem_extendedAffineWeylGroup_iff.1 (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup
      b hf)).1

/-- `Ω_Y` is a subgroup of `Ω`. -/
theorem latticeFundamentalAlcoveStabilizer_le_fundamentalAlcoveStabilizer :
    P.latticeFundamentalAlcoveStabilizer b Y hQ hP ≤ P.fundamentalAlcoveStabilizer b :=
  inf_le_left

/-- `Ω_Y` is a subgroup of `W_Y`. -/
theorem latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup :
    P.latticeFundamentalAlcoveStabilizer b Y hQ hP ≤ P.latticeAffineWeylGroup Y hQ hP :=
  inf_le_right

/-- `Ω_Y` normalizes the affine Weyl group, since `W_aff` is normal in `W_Y`. -/
theorem latticeFundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup :
    P.latticeFundamentalAlcoveStabilizer b Y hQ hP ≤
      Subgroup.normalizer (P.affineWeylGroup : Set (N ≃ᵃ[R] N)) :=
  (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP).trans
    (Subgroup.le_normalizer_of_normal_subgroupOf
      (P.affineWeylGroup_le_latticeAffineWeylGroup hQ hP))

/-- The homomorphism from `Ω_Y` to `Y / Q∨` taking an element to the class of its translation part
`ω 0` modulo the coroot lattice: the restriction of `RootPairing.latticeAffineWeylGroupToQuotient`
to `Ω_Y`. -/
def latticeFundamentalAlcoveStabilizerToQuotient :
    P.latticeFundamentalAlcoveStabilizer b Y hQ hP →*
      Multiplicative (Y ⧸ (P.corootSpan ℤ).comap Y.subtype) :=
  (P.latticeAffineWeylGroupToQuotient hQ hP).comp
    (Subgroup.inclusion (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP))

@[simp]
lemma latticeFundamentalAlcoveStabilizerToQuotient_apply
    (ω : P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    latticeFundamentalAlcoveStabilizerToQuotient b hQ hP ω =
      .ofAdd (Submodule.Quotient.mk ⟨ω.val 0, ((mem_latticeFundamentalAlcoveStabilizer b hQ hP).1
        ω.property).2⟩) :=
  P.latticeAffineWeylGroupToQuotient_apply hQ hP _

end Lattice

variable [P.IsCrystallographic]

/-- The stabilizer `Ω` of the fundamental alcove normalizes the affine Weyl group. -/
theorem fundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup :
    P.fundamentalAlcoveStabilizer b ≤
      Subgroup.normalizer (P.affineWeylGroup : Set (N ≃ᵃ[R] N)) :=
  (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b).trans
    P.extendedAffineWeylGroup_le_normalizer_affineWeylGroup

section Lattice

variable {Y : Submodule ℤ N} (hQ : P.corootSpan ℤ ≤ Y) (hP : Y ≤ P.coweightLattice)

/-- For the coweight lattice, `Ω_{P∨}` is the stabilizer `Ω` of the fundamental alcove. -/
theorem latticeFundamentalAlcoveStabilizer_coweightLattice :
    P.latticeFundamentalAlcoveStabilizer b P.coweightLattice P.corootSpan_le_coweightLattice
      le_rfl = P.fundamentalAlcoveStabilizer b :=
  Subgroup.ext fun f ↦ by
    rw [mem_latticeFundamentalAlcoveStabilizer]
    exact and_iff_left_of_imp fun hf ↦ apply_zero_mem_coweightLattice b ⟨f, hf⟩

end Lattice

end CommRing

section Field

variable {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base) [LinearOrder R] [IsStrictOrderedRing R]
  [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **`W_aff ∩ Ω` is trivial**: the affine Weyl group acts freely on the alcoves. -/
theorem affineWeylGroup_inf_fundamentalAlcoveStabilizer :
    P.affineWeylGroup ⊓ P.fundamentalAlcoveStabilizer b = ⊥ :=
  disjoint_iff.1 <| Subgroup.subgroupOf_eq_bot.1 <|
    affineWeylGroup_subgroupOf_fundamentalAlcoveStabilizer_eq_bot b

section Lattice

variable {Y : Submodule ℤ N} (hQ : P.corootSpan ℤ ≤ Y) (hP : Y ≤ P.coweightLattice)

/-- **`W_aff ∩ Ω_Y` is trivial.** -/
theorem affineWeylGroup_inf_latticeFundamentalAlcoveStabilizer :
    P.affineWeylGroup ⊓ P.latticeFundamentalAlcoveStabilizer b Y hQ hP = ⊥ :=
  eq_bot_mono (inf_le_inf_left _
    (latticeFundamentalAlcoveStabilizer_le_fundamentalAlcoveStabilizer b hQ hP))
    (affineWeylGroup_inf_fundamentalAlcoveStabilizer b)

/-- For the coroot lattice, `Ω_{Q∨}` is trivial. -/
theorem latticeFundamentalAlcoveStabilizer_corootSpan :
    P.latticeFundamentalAlcoveStabilizer b (P.corootSpan ℤ) le_rfl
      P.corootSpan_le_coweightLattice = ⊥ := by
  rw [latticeFundamentalAlcoveStabilizer, latticeAffineWeylGroup_corootSpan, inf_comm,
    affineWeylGroup_inf_fundamentalAlcoveStabilizer]

/-- **The homomorphism `Ω_Y → Y / Q∨` is injective**: its kernel lies in `W_aff ∩ Ω_Y`, which is
trivial. -/
theorem latticeFundamentalAlcoveStabilizerToQuotient_injective :
    Injective (latticeFundamentalAlcoveStabilizerToQuotient b hQ hP) := by
  refine (injective_iff_map_eq_one _).2 fun ω hω ↦ Subtype.ext ?_
  have h : Subgroup.inclusion (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ
      hP) ω ∈ (P.latticeAffineWeylGroupToQuotient hQ hP).ker := hω
  rw [ker_latticeAffineWeylGroupToQuotient, Subgroup.mem_subgroupOf] at h
  have hmem : (ω : N ≃ᵃ[R] N) ∈
      P.affineWeylGroup ⊓ P.latticeFundamentalAlcoveStabilizer b Y hQ hP :=
    ⟨h, ω.property⟩
  rwa [affineWeylGroup_inf_latticeFundamentalAlcoveStabilizer, Subgroup.mem_bot] at hmem

end Lattice

variable [Archimedean R]

/-! ### `W_ext = W_aff ⋊ Ω` -/

variable (P) in
/-- **The extended affine Weyl group is the semidirect product `W_aff ⋊ Ω`** of the affine Weyl
group and the stabilizer of the fundamental alcove, which acts on `W_aff` by conjugation; the
isomorphism is multiplication `(g, ω) ↦ g ω`. -/
noncomputable def extendedAffineWeylGroupMulEquiv :
    P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion (fundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b))]
      P.fundamentalAlcoveStabilizer b ≃* P.extendedAffineWeylGroup :=
  (SemidirectProduct.mulEquivSup _ (affineWeylGroup_inf_fundamentalAlcoveStabilizer b)).trans
    (MulEquiv.subgroupCongr (affineWeylGroup_sup_fundamentalAlcoveStabilizer b))

@[simp]
theorem coe_extendedAffineWeylGroupMulEquiv_apply
    (x : P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion (fundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b))]
      P.fundamentalAlcoveStabilizer b) :
    (P.extendedAffineWeylGroupMulEquiv b x : N ≃ᵃ[R] N) = x.left * x.right :=
  SemidirectProduct.coe_mulEquivSup_apply _ _ x

/-- **The inverse of `W_aff ⋊ Ω ≃* W_ext`**: its `Ω`-component is the element of `Ω` whose
translation part is congruent to that of `f` modulo `Q∨`, and the `W_aff`-component is then
determined by `g ω = f`. -/
theorem extendedAffineWeylGroupMulEquiv_symm_apply_right (f : P.extendedAffineWeylGroup) :
    ((P.extendedAffineWeylGroupMulEquiv b).symm f).right =
      (P.fundamentalAlcoveStabilizerEquivQuotient b).symm
        (P.extendedAffineWeylGroupToQuotient f) := by
  rw [MulEquiv.eq_symm_apply, fundamentalAlcoveStabilizerEquivQuotient_apply]
  set x := (P.extendedAffineWeylGroupMulEquiv b).symm f
  have hf : f = ⟨x.left, P.affineWeylGroup_le_extendedAffineWeylGroup x.left.property⟩ *
      ⟨x.right, P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b x.right.property⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← coe_extendedAffineWeylGroupMulEquiv_apply,
      MulEquiv.apply_symm_apply]
  -- The `W_aff`-factor lies in the kernel of `W_ext → P∨ / Q∨`.
  have hleft : P.extendedAffineWeylGroupToQuotient
      ⟨x.left, P.affineWeylGroup_le_extendedAffineWeylGroup x.left.property⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ker_extendedAffineWeylGroupToQuotient, Subgroup.mem_subgroupOf]
    exact x.left.property
  rw [hf, map_mul, hleft, one_mul, fundamentalAlcoveStabilizerToQuotient_apply,
    extendedAffineWeylGroupToQuotient_apply]

/-- The `W_aff`-component of the inverse of `W_aff ⋊ Ω ≃* W_ext` at `f` is `f ω⁻¹`, where `ω` is
its `Ω`-component. -/
theorem coe_extendedAffineWeylGroupMulEquiv_symm_apply_left (f : P.extendedAffineWeylGroup) :
    (((P.extendedAffineWeylGroupMulEquiv b).symm f).left : N ≃ᵃ[R] N) =
      f * (((P.extendedAffineWeylGroupMulEquiv b).symm f).right : N ≃ᵃ[R] N)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← coe_extendedAffineWeylGroupMulEquiv_apply,
    MulEquiv.apply_symm_apply]

/-! ### `W_Y = W_aff ⋊ Ω_Y` and `Ω_Y ≃ Y / Q∨` -/

section Lattice

variable {Y : Submodule ℤ N} (hQ : P.corootSpan ℤ ≤ Y) (hP : Y ≤ P.coweightLattice)

/-- **`W_aff ⊔ Ω_Y = W_Y`**: the affine Weyl group is transitive on the alcoves, so it carries the
alcove `f(A)` back to `A` for every `f ∈ W_Y`. -/
theorem affineWeylGroup_sup_latticeFundamentalAlcoveStabilizer :
    P.affineWeylGroup ⊔ P.latticeFundamentalAlcoveStabilizer b Y hQ hP =
      P.latticeAffineWeylGroup Y hQ hP := by
  refine le_antisymm (sup_le (P.affineWeylGroup_le_latticeAffineWeylGroup hQ hP)
    (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP)) fun f hf ↦ ?_
  obtain ⟨g, hg, hgf⟩ := exists_mem_affineWeylGroup_mul_mem_fundamentalAlcoveStabilizer b
    (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP hf)
  have hgf' : g * f ∈ P.latticeFundamentalAlcoveStabilizer b Y hQ hP :=
    ⟨hgf, mul_mem (P.affineWeylGroup_le_latticeAffineWeylGroup hQ hP hg) hf⟩
  simpa using mul_mem (Subgroup.mem_sup_left (inv_mem hg)) (Subgroup.mem_sup_right hgf')

/-- **The homomorphism `Ω_Y → Y / Q∨` is onto**: every `y ∈ Y` is congruent modulo `Q∨` to the
translation part of an element of `Ω`, and that translation part then lies in `Y`. -/
theorem latticeFundamentalAlcoveStabilizerToQuotient_surjective :
    Surjective (latticeFundamentalAlcoveStabilizerToQuotient b hQ hP) := by
  intro q
  induction q using Multiplicative.rec with | ofAdd q => ?_
  induction q using Submodule.Quotient.induction_on with | H y => ?_
  obtain ⟨ω, hω, hωy⟩ := exists_mem_fundamentalAlcoveStabilizer_sub_mem_corootSpan b (hP y.property)
  have hω0 : ω 0 ∈ Y := by simpa using add_mem (hQ hωy) y.property
  refine ⟨⟨ω, (mem_latticeFundamentalAlcoveStabilizer b hQ hP).2 ⟨hω, hω0⟩⟩, ?_⟩
  rw [latticeFundamentalAlcoveStabilizerToQuotient_apply, Multiplicative.ofAdd.injective.eq_iff,
    Submodule.Quotient.eq, Submodule.mem_comap]
  exact hωy

variable (P Y) in
/-- **`Ω_Y ≃ Y / Q∨`.** The stabilizer of the fundamental alcove in `W_Y` is isomorphic to the
quotient of `Y` by the coroot lattice, through the class of the translation part. -/
noncomputable def latticeFundamentalAlcoveStabilizerEquivQuotient :
    P.latticeFundamentalAlcoveStabilizer b Y hQ hP ≃*
      Multiplicative (Y ⧸ (P.corootSpan ℤ).comap Y.subtype) :=
  MulEquiv.ofBijective (latticeFundamentalAlcoveStabilizerToQuotient b hQ hP)
    ⟨latticeFundamentalAlcoveStabilizerToQuotient_injective b hQ hP,
      latticeFundamentalAlcoveStabilizerToQuotient_surjective b hQ hP⟩

@[simp]
lemma latticeFundamentalAlcoveStabilizerEquivQuotient_apply
    (ω : P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    P.latticeFundamentalAlcoveStabilizerEquivQuotient b Y hQ hP ω =
      latticeFundamentalAlcoveStabilizerToQuotient b hQ hP ω :=
  (rfl)

variable (P Y) in
/-- **`W_Y` is the semidirect product `W_aff ⋊ Ω_Y`** of the affine Weyl group and the stabilizer
of the fundamental alcove in `W_Y`, which acts on `W_aff` by conjugation; the isomorphism is
multiplication `(g, ω) ↦ g ω`. -/
noncomputable def latticeAffineWeylGroupMulEquiv :
    P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion
        (latticeFundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b hQ hP))]
      P.latticeFundamentalAlcoveStabilizer b Y hQ hP ≃* P.latticeAffineWeylGroup Y hQ hP :=
  (SemidirectProduct.mulEquivSup _
    (affineWeylGroup_inf_latticeFundamentalAlcoveStabilizer b hQ hP)).trans
    (MulEquiv.subgroupCongr (affineWeylGroup_sup_latticeFundamentalAlcoveStabilizer b hQ hP))

@[simp]
theorem coe_latticeAffineWeylGroupMulEquiv_apply
    (x : P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion
        (latticeFundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b hQ hP))]
      P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    (P.latticeAffineWeylGroupMulEquiv b Y hQ hP x : N ≃ᵃ[R] N) = x.left * x.right :=
  SemidirectProduct.coe_mulEquivSup_apply _ _ x

/-- **The inverse of `W_aff ⋊ Ω_Y ≃* W_Y`**: its `Ω_Y`-component is the element of `Ω_Y` whose
translation part is congruent to that of `f` modulo `Q∨`, and the `W_aff`-component is then
determined by `g ω = f`. -/
theorem latticeAffineWeylGroupMulEquiv_symm_apply_right (f : P.latticeAffineWeylGroup Y hQ hP) :
    ((P.latticeAffineWeylGroupMulEquiv b Y hQ hP).symm f).right =
      (P.latticeFundamentalAlcoveStabilizerEquivQuotient b Y hQ hP).symm
        (P.latticeAffineWeylGroupToQuotient hQ hP f) := by
  rw [MulEquiv.eq_symm_apply, latticeFundamentalAlcoveStabilizerEquivQuotient_apply]
  set x := (P.latticeAffineWeylGroupMulEquiv b Y hQ hP).symm f
  have hf : f = ⟨x.left, P.affineWeylGroup_le_latticeAffineWeylGroup hQ hP x.left.property⟩ *
      Subgroup.inclusion (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP)
        x.right := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inclusion, ← coe_latticeAffineWeylGroupMulEquiv_apply,
      MulEquiv.apply_symm_apply]
  -- The `W_aff`-factor lies in the kernel of `W_Y → Y / Q∨`.
  have hleft : P.latticeAffineWeylGroupToQuotient hQ hP
      ⟨x.left, P.affineWeylGroup_le_latticeAffineWeylGroup hQ hP x.left.property⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ker_latticeAffineWeylGroupToQuotient, Subgroup.mem_subgroupOf]
    exact x.left.property
  rw [hf, map_mul, hleft, one_mul]
  simp only [latticeFundamentalAlcoveStabilizerToQuotient_apply,
    latticeAffineWeylGroupToQuotient_apply, Subgroup.coe_inclusion]

/-- The `W_aff`-component of the inverse of `W_aff ⋊ Ω_Y ≃* W_Y` at `f` is `f ω⁻¹`, where `ω` is
its `Ω_Y`-component. -/
theorem coe_latticeAffineWeylGroupMulEquiv_symm_apply_left (f : P.latticeAffineWeylGroup Y hQ hP) :
    (((P.latticeAffineWeylGroupMulEquiv b Y hQ hP).symm f).left : N ≃ᵃ[R] N) =
      f * (((P.latticeAffineWeylGroupMulEquiv b Y hQ hP).symm f).right : N ≃ᵃ[R] N)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← coe_latticeAffineWeylGroupMulEquiv_apply,
    MulEquiv.apply_symm_apply]

end Lattice

end Field

end RootPairing
