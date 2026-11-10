/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Submodule.Finrank

/-!
# Elementary identities for Lie algebra weights

This file records general identities for weights that are used by several parts of the Lie algebra
weight-space theory. The transport and finrank identities hold over any commutative ring.

## Main results

* `LieModule.weightSpace_zero`: the zero-weight space is the submodule of invariant vectors.
* `LieModule.map_weightSpace_le`: a Lie-module homomorphism preserves each weight space.
* `LieModule.comap_weightSpace_eq_of_injective`: the preimage under an injective Lie-module
  homomorphism is the corresponding source weight space.
* `LieModule.map_weightSpace_eq_of_injective`: an injective Lie-module homomorphism identifies a
  weight space with the intersection of the target weight space and its range.
* `LieModule.map_weightSpace_eq`: a Lie-module equivalence maps each weight space onto the
  corresponding weight space.
* `LieModule.isTriangularizable_of_iSup_genWeightSpace_eq_top`: a module spanned by its
  generalized weight spaces is triangularizable, over any commutative ring and without finiteness.
* `LieModule.genWeightSpaceOf_eq_iSup_genWeightSpace`: for a finite-dimensional triangularizable
  module, a generalized eigenspace of one element is the sum of the generalized weight spaces of
  the weights taking that eigenvalue there.
* `LieModuleEquiv.finrank_weightSpace_eq`: equivalent Lie modules have weight spaces of equal
  dimension.
* `LieSubmodule.toSubmodule_map_weightSpace_incl`: inclusion identifies a submodule's weight space
  with its intersection with the ambient weight space.
* `LieSubmodule.finrank_inf_weightSpace`: that intersection has the dimension of the submodule's
  weight space.
* `LieSubmodule.toSubmodule_map_genWeightSpace_incl`: inclusion identifies a submodule's
  generalized weight space with its intersection with the ambient generalized weight space.
* `LieSubmodule.finrank_inf_genWeightSpace`: that intersection has the dimension of the
  submodule's generalized weight space.
* `TauCeti.toSubmodule_rootSpace_eq_of_isZero`: the root space of a zero weight is the Cartan
  subalgebra.
* `LinearMap.map_lie_eq_of_forall_mem_rootSpace`, `LinearMap.involutive_of_forall_mem_rootSpace`:
  a linear map respects the bracket, respectively is an involution, as soon as it does so on root
  spaces.
* `LinearMap.map_lie_eq_of_isZero_of_isNonZero`: bracket compatibility on a zero-weight vector
  and a root vector.
* `TauCeti.Weight.coe_neg_eq_add_of_coe_eq_add`: reading a vanishing sum of four weights as an
  equation between opposite pair sums.
* `LieSubalgebra.exists_forall_root_apply_ne_zero`: some element of a Cartan subalgebra is nonzero
  under every root.
* `LieSubalgebra.span_rootVectors_eq_top`: root vectors bracketed with a point at which no root
  vanishes, together with a basis of the Cartan subalgebra, span the Lie algebra.
* `LieSubalgebra.exists_nonzero_rootVectors`: a nonzero vector in each root space, with a
  nilpotency degree of its adjoint action.
* `LieModuleHom.exists_mem_weight_of_injective`: if the weights of `N` lie in a set of linear
  forms, then so do the weights of any module embedding in `N`.

## References

The weight-space transport family follows the generalized-weight-space API
`LieModule.map_genWeightSpace_le` through `LieModule.map_genWeightSpace_eq` in
`Mathlib.Algebra.Lie.Weights.Basic`.
-/

public section

namespace Module.Basis

open LieModule

/-- A linear weight equation can be checked on a basis of the Lie algebra. -/
theorem mem_weightSpace_iff_forall_basis
    {R L M ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    (b : Module.Basis ι R L) (χ : Module.Dual R L) (m : M) :
    m ∈ weightSpace M (χ : L → R) ↔ ∀ i, ⁅b i, m⁆ = χ (b i) • m := by
  rw [mem_weightSpace]
  constructor
  · exact fun h i => h (b i)
  · intro h
    have heq : (toEnd R L M).flip m = χ.smulRight m := b.ext h
    exact fun x => LinearMap.congr_fun heq x

end Module.Basis

namespace LieModule

variable {R L M M₂ : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]

variable (M) in
/-- The zero-weight space is the submodule of invariant vectors. -/
@[simp]
theorem weightSpace_zero : weightSpace M (0 : L → R) = maxTrivSubmodule R L M := by
  ext m
  simp [mem_weightSpace, mem_maxTrivSubmodule]

variable (M) in
/-- The weight space of the zero linear form is the submodule of invariant vectors. -/
@[simp]
theorem weightSpace_coe_zero :
    weightSpace M ⇑(0 : Module.Dual R L) = maxTrivSubmodule R L M := by
  have hzero : ⇑(0 : Module.Dual R L) = (0 : L → R) := funext LinearMap.zero_apply
  rw [hzero, weightSpace_zero]

/-- A morphism of Lie modules sends a weight space into the corresponding weight space. -/
theorem map_weightSpace_le (f : LieModuleHom R L M M₂) (χ : L → R) :
    (weightSpace M χ).map f ≤ weightSpace M₂ χ := by
  intro y hy
  rw [LieSubmodule.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [mem_weightSpace] at hx ⊢
  intro l
  rw [← f.map_lie, hx l, map_smul]

/-- The preimage of a weight space under an injective Lie-module homomorphism is the corresponding
weight space in the source. -/
theorem comap_weightSpace_eq_of_injective {f : LieModuleHom R L M M₂} (χ : L → R)
    (hf : Function.Injective f) :
    (weightSpace M₂ χ).comap f = weightSpace M χ := by
  apply le_antisymm
  · intro m hm
    rw [LieSubmodule.mem_comap, mem_weightSpace] at hm
    rw [mem_weightSpace]
    intro x
    apply hf
    rw [f.map_lie, map_smul, hm x]
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact map_weightSpace_le f χ

/-- Under an injective Lie-module homomorphism, the image of a weight space is the intersection of
the corresponding target weight space with the range. -/
theorem map_weightSpace_eq_of_injective {f : LieModuleHom R L M M₂} (χ : L → R)
    (hf : Function.Injective f) :
    (weightSpace M χ).map f = weightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm
    (le_inf_iff.mpr ⟨map_weightSpace_le f χ, LieSubmodule.map_le_range f⟩) ?_
  rintro y ⟨hy, ⟨x, rfl⟩⟩
  simp only [← comap_weightSpace_eq_of_injective χ hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap] at hy ⊢
  exact ⟨x, hy, rfl⟩

/-- A Lie-module equivalence maps a weight space onto the corresponding weight space. -/
theorem map_weightSpace_eq (e : LieModuleEquiv R L M M₂) (χ : L → R) :
    (weightSpace M χ).map e = weightSpace M₂ χ := by
  simp [map_weightSpace_eq_of_injective χ e.injective]

section Triangularizable

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **A module spanned by its generalized weight spaces is triangularizable.** The generalized
weight space of `χ` lies in the generalized `χ x`-eigenspace of each `x : L`, so if the weight
spaces span `M` then so do the generalized eigenspaces of every `x`. No finiteness is assumed; for a
finite-dimensional module over a field this is the converse of
`LieModule.iSup_genWeightSpace_eq_top`. -/
theorem isTriangularizable_of_iSup_genWeightSpace_eq_top
    (h : ⨆ χ : L → R, genWeightSpace M χ = ⊤) : IsTriangularizable R L M := by
  have h' := congrArg LieSubmodule.toSubmodule h
  rw [LieSubmodule.iSup_toSubmodule, LieSubmodule.top_toSubmodule] at h'
  refine ⟨fun x => top_unique (h' ▸ iSup_le fun χ => le_iSup_of_le (χ x) fun m hm => ?_)⟩
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr
    ((mem_genWeightSpaceOf M (χ x) x m).mp (genWeightSpace_le_genWeightSpaceOf M x χ hm))

end Triangularizable

section Field

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  [IsTriangularizable K L M]

/-- **A generalized eigenspace of one element is the sum of the matching weight spaces.** The
generalized `μ`-eigenspace of `x` is spanned by the generalized weight spaces of the weights taking
the value `μ` at `x`. -/
theorem genWeightSpaceOf_eq_iSup_genWeightSpace (μ : K) (x : L) :
    genWeightSpaceOf M μ x = ⨆ (χ : Weight K L M) (_ : χ x = μ), genWeightSpace M χ := by
  refine le_antisymm ?_ (iSup₂_le fun χ hχ ↦ hχ ▸ genWeightSpace_le_genWeightSpaceOf M x χ)
  refine (eq_iSup_inf_genWeightSpace K L M (genWeightSpaceOf M μ x)).le.trans
    (iSup_le fun χ ↦ ?_)
  by_cases hχ : χ x = μ
  · exact inf_le_right.trans (le_iSup₂_of_le χ hχ le_rfl)
  · have hdisj := (disjoint_genWeightSpaceOf K L M (Ne.symm hχ)).mono_right
      (genWeightSpace_le_genWeightSpaceOf M x χ)
    exact hdisj.eq_bot.le.trans bot_le

end Field

end LieModule

namespace LieModuleEquiv

open LieModule Module

/-- **Weight-space finrank is an isomorphism invariant.** An equivalence of Lie modules over a
commutative ring carries the `χ`-weight space of one module onto that of the other. -/
theorem finrank_weightSpace_eq
    {K L M P : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [AddCommGroup P] [Module K P] [LieRingModule L P] [LieModule K L P]
    (e : M ≃ₗ⁅K,L⁆ P) (χ : L → K) :
    finrank K (weightSpace M χ) = finrank K (weightSpace P χ) := by
  rw [← LieModule.map_weightSpace_eq e χ]
  exact (LieSubmodule.equivMapOfInjective
    (weightSpace M χ) e.injective).toLinearEquiv.finrank_eq

end LieModuleEquiv

namespace LieSubmodule

open LieModule Module

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {H : LieSubalgebra R L}

/-- Inclusion of a Lie submodule identifies its weight space with the intersection of the ambient
weight space and its carrier. -/
theorem toSubmodule_map_weightSpace_incl (N : LieSubmodule R L M) (χ : H → R) :
    ((weightSpace ↥N χ).map (N.incl.restrictLie H)).toSubmodule
      = (weightSpace M χ).toSubmodule ⊓ N.toSubmodule := by
  rw [LieModule.map_weightSpace_eq_of_injective χ (injective_incl N),
    LieSubmodule.inf_toSubmodule]
  congr 1
  ext x
  simp

/-- The intersection of an ambient weight space with a Lie submodule has the dimension of the
corresponding weight space in the submodule. -/
theorem finrank_inf_weightSpace {K : Type*} [CommRing K] [LieAlgebra K L]
    [Module K M] [LieModule K L M] {H : LieSubalgebra K L}
    (N : LieSubmodule K L M) (χ : H → K) :
    finrank K ((weightSpace M χ).toSubmodule ⊓ N.toSubmodule : Submodule K M)
      = finrank K (weightSpace ↥N χ) := by
  rw [← N.toSubmodule_map_weightSpace_incl χ, LieSubmodule.finrank_toSubmodule]
  exact (LieSubmodule.equivMapOfInjective (weightSpace ↥N χ)
    (f := N.incl.restrictLie H) (injective_incl N)).toLinearEquiv.finrank_eq.symm

/-- Inclusion of a Lie submodule identifies its generalized weight space with the intersection of
the ambient generalized weight space and its carrier. -/
theorem toSubmodule_map_genWeightSpace_incl [LieRing.IsNilpotent H]
    (N : LieSubmodule R L M) (χ : H → R) :
    ((genWeightSpace ↥N χ).map (N.incl.restrictLie H)).toSubmodule
      = (genWeightSpace M χ).toSubmodule ⊓ N.toSubmodule := by
  rw [LieModule.map_genWeightSpace_eq_of_injective
      (f := N.incl.restrictLie H) (injective_incl N),
    LieSubmodule.inf_toSubmodule]
  congr 1
  ext x
  simp

/-- The intersection of an ambient generalized weight space with a Lie submodule has the
dimension of the corresponding generalized weight space in the submodule. -/
theorem finrank_inf_genWeightSpace {K : Type*} [CommRing K] [LieAlgebra K L]
    [Module K M] [LieModule K L M] {H : LieSubalgebra K L} [LieRing.IsNilpotent H]
    (N : LieSubmodule K L M) (χ : H → K) :
    finrank K ((genWeightSpace M χ).toSubmodule ⊓ N.toSubmodule : Submodule K M)
      = finrank K (genWeightSpace ↥N χ) := by
  rw [← N.toSubmodule_map_genWeightSpace_incl χ, LieSubmodule.finrank_toSubmodule]
  exact (LieSubmodule.equivMapOfInjective (genWeightSpace ↥N χ)
    (f := N.incl.restrictLie H) (injective_incl N)).toLinearEquiv.finrank_eq.symm

end LieSubmodule

namespace LieModule.Weight

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- Consecutive weights on an ascending string differ by its step root. -/
theorem coe_eq_add_of_coe_eq_add_natCast_smul_succ
    (δ : Weight K H L) {α β γ : Weight K H L} {n : ℕ}
    (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K))
    (hδ : (δ : H → K) = (β : H → K) + ((n + 1 : ℕ) : K) • (α : H → K)) :
    (δ : H → K) = (α : H → K) + γ := by
  rw [hδ, hγ]
  push_cast
  module

end LieModule.Weight

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- If four weights sum to zero and a weight `μ` names the sum of the first two, then `-μ` names
the sum of the last two. -/
theorem Weight.coe_neg_eq_add_of_coe_eq_add {μ : Weight K H L} {a b c d : H → K}
    (hsum : a + b + c + d = 0) (hμ : (μ : H → K) = a + b) :
    ((-μ : Weight K H L) : H → K) = c + d := by
  funext y
  have hy := congrFun hsum y
  simp only [Weight.coe_neg, hμ, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hy ⊢
  linear_combination -hy

omit [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L] in
/-- The root space of a zero weight is the Cartan subalgebra. -/
theorem toSubmodule_rootSpace_eq_of_isZero {χ : Weight K H L} (hχ : χ.IsZero) :
    (rootSpace H χ).toSubmodule = H.toSubmodule := by
  -- `Weight.IsZero` is the vanishing of the coercion, but only up to unfolding the definition.
  have hχcoe : (χ : H → K) = 0 := hχ
  simp only [hχcoe, rootSpace_zero_eq K L H]
  simp

omit [LieAlgebra.IsKilling K L] in
/-- A linear map from `L` to a Lie algebra respects the bracket as soon as it does so on every
pair of root vectors, since the root spaces span `L`. -/
theorem _root_.LinearMap.map_lie_eq_of_forall_mem_rootSpace {M : Type*} [LieRing M]
    [LieAlgebra K M] (f : L →ₗ[K] M)
    (h : ∀ (χ₁ χ₂ : Weight K H L) (v : L), v ∈ rootSpace H χ₁ → ∀ w : L, w ∈ rootSpace H χ₂ →
      f ⁅v, w⁆ = ⁅f v, f w⁆) (v w : L) : f ⁅v, w⁆ = ⁅f v, f w⁆ := by
  have htop : ⨆ χ : Weight K H L, (rootSpace H χ).toSubmodule = ⊤ :=
    LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' K H L)
  -- Extend from weight vectors by linearity in each argument.
  have hright : ∀ (χ₁ : Weight K H L) (v : L), v ∈ rootSpace H χ₁ → ∀ w : L,
      f ⁅v, w⁆ = ⁅f v, f w⁆ := by
    intro χ₁ v hv w
    have hle : (⊤ : Submodule K L) ≤
        LinearMap.eqLocus (f.comp (LieAlgebra.ad K L v)) ((LieAlgebra.ad K M (f v)).comp f) := by
      rw [← htop]
      exact iSup_le fun χ₂ u hu ↦ h χ₁ χ₂ v hv u hu
    exact hle trivial
  have hle : (⊤ : Submodule K L) ≤
      LinearMap.eqLocus (f.comp (LieAlgebra.ad K L w)) ((LieAlgebra.ad K M (f w)).comp f) := by
    rw [← htop]
    exact iSup_le fun χ₁ u hu ↦ LinearMap.map_lie_swap (hright χ₁ u hu w)
  exact LinearMap.map_lie_swap (hle trivial)

omit [LieAlgebra.IsKilling K L] in
/-- A linear map of `L` that squares to the identity on each root space is an involution. -/
theorem _root_.LinearMap.involutive_of_forall_mem_rootSpace (f : L →ₗ[K] L)
    (h : ∀ (χ : Weight K H L) (v : L), v ∈ rootSpace H χ → f (f v) = v) :
    Function.Involutive f := by
  have htop : ⨆ χ : Weight K H L, (rootSpace H χ).toSubmodule = ⊤ :=
    LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' K H L)
  intro v
  have hle : (⊤ : Submodule K L) ≤ LinearMap.eqLocus (f.comp f) LinearMap.id := by
    rw [← htop]
    exact iSup_le fun χ u hu ↦ h χ u hu
  exact hle trivial

/-- A linear map that negates the Cartan subalgebra and sends each nonzero root space into its
opposite root space respects the bracket of a zero-weight vector with a root vector: a Cartan
element brackets with a weight vector through its weight. -/
theorem _root_.LinearMap.map_lie_eq_of_isZero_of_isNonZero [PerfectField K] (ω : L →ₗ[K] L)
    (hzero : ∀ χ : Weight K H L, χ.IsZero → ∀ v : L, v ∈ rootSpace H χ → ω v = -v)
    (hωmem : ∀ χ : Weight K H L, χ.IsNonZero → ∀ v : L, v ∈ rootSpace H χ →
      ω v ∈ rootSpace H (-χ))
    {χ₁ χ₂ : Weight K H L} (hχ₁ : χ₁.IsZero) (hχ₂ : χ₂.IsNonZero) {v : L}
    (hv : v ∈ rootSpace H χ₁) {w : L} (hw : w ∈ rootSpace H χ₂) :
    ω ⁅v, w⁆ = ⁅ω v, ω w⁆ := by
  have hvH : v ∈ H := by
    have := toSubmodule_rootSpace_eq_of_isZero (K := K) (L := L) (H := H) hχ₁
    exact (SetLike.ext_iff.mp this v).mp hv
  have hlie : ⁅v, w⁆ = (χ₂ : H → K) ⟨v, hvH⟩ • w :=
    lie_eq_smul_of_mem_rootSpace hw ⟨v, hvH⟩
  have hstep : ⁅v, ω w⁆ = ((-χ₂ : Weight K H L) : H → K) ⟨v, hvH⟩ • ω w :=
    lie_eq_smul_of_mem_rootSpace (hωmem χ₂ hχ₂ w hw) ⟨v, hvH⟩
  rw [hlie, map_smul, hzero χ₁ hχ₁ v hv, neg_lie, hstep]
  simp

end TauCeti

namespace LieSubalgebra

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

variable (H : LieSubalgebra K L)

variable [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The root vectors bracketed with a point at which no root vanishes, together with a basis of the
Cartan subalgebra, span `L`. -/
theorem span_rootVectors_eq_top {κ : Type*} [Finite κ]
    (e : H.root → L) (he : ∀ α, e α ∈ rootSpace H α.1) (he0 : ∀ α, e α ≠ 0) (h₀ : H)
    (hh₀ : ∀ α ∈ H.root, (α : H → K) h₀ ≠ 0) (bH : Module.Basis κ K H) :
    Submodule.span K (Set.range (Sum.elim (fun α ↦ ⁅e α, (h₀ : L)⁆) fun j ↦ (bH j : L))) = ⊤ := by
  have := Fintype.ofFinite κ
  rw [eq_top_iff, ← LieSubmodule.top_toSubmodule (R := K) (L := H) (M := L),
    ← iSup_genWeightSpace_eq_top' K H L,
    LieSubmodule.iSup_toSubmodule, iSup_le_iff]
  intro χ z hz
  rw [LieSubmodule.mem_toSubmodule] at hz
  by_cases hχ : χ.IsZero
  · -- `rootSpace H χ` is by definition the weight space `genWeightSpace L χ`.
    have hzH : z ∈ rootSpace H 0 := by rwa [← (Weight.coe_eq_zero_iff χ).mpr hχ]
    rw [rootSpace_zero_eq K L H, LieSubalgebra.mem_toLieSubmodule] at hzH
    lift z to H using hzH
    rw [← bH.sum_repr z, AddSubmonoidClass.coe_finsetSum]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  · set α : H.root := ⟨χ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχ⟩⟩
    obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨e α, he α⟩ : rootSpace H χ)
      (by simpa [Subtype.ext_iff] using he0 α)).mp (finrank_rootSpace_eq_one χ hχ) ⟨z, hz⟩
    have hz' : z = r • e α := by simpa [Subtype.ext_iff] using hr.symm
    have hbr : ⁅e α, (h₀ : L)⁆ = -(χ h₀) • e α := by
      rw [← lie_skew, ← LieSubalgebra.coe_bracket_of_module,
        lie_eq_smul_of_mem_rootSpace (he α) h₀, neg_smul]
    have hχh₀ : χ h₀ ≠ 0 := hh₀ α α.2
    have he' : e α = (-(χ h₀))⁻¹ • ⁅e α, (h₀ : L)⁆ := by
      rw [hbr, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hχh₀), one_smul]
    rw [hz', he']
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Sum.inl α, rfl⟩))

omit [LieAlgebra.IsKilling K L] in
/-- A nonzero root vector in each root space, with a nilpotency degree of its adjoint action. -/
theorem exists_nonzero_rootVectors :
    ∃ (e : H.root → L), (∀ α, e α ∈ rootSpace H α.1) ∧ (∀ α, e α ≠ 0) ∧
      ∃ n : H.root → ℕ, ∀ α, ad K L (e α) ^ n α = 0 := by
  have hα0 (α : H.root) : α.1.IsNonZero := (Finset.mem_filter.mp α.2).2
  choose e he he0 using fun α : H.root ↦ α.1.exists_ne_zero
  have hnil (α : H.root) : IsNilpotent (ad K L (e α)) :=
    isNilpotent_ad_of_mem_rootSpace H (fun h ↦ hα0 α ((Weight.coe_eq_zero_iff _).mp h)) (he α)
  choose n hn using hnil
  exact ⟨e, he, he0, n, hn⟩

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- **A generic element of a Cartan subalgebra avoids every root hyperplane.** Since the root set
is finite and each root is a nonzero linear functional, finite hyperplane avoidance over the
infinite field `K` supplies one `h : H` on which every root is nonzero. -/
theorem exists_forall_root_apply_ne_zero [Infinite K]
    [LieModule.LinearWeights K H L] :
    ∃ h : H, ∀ α ∈ H.root, (α : H → K) h ≠ 0 := by
  let f : H.root → Module.Dual K H := fun α ↦ (α.1 : H →ₗ[K] K)
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f fun α ↦ by
    simpa [f] using DFunLike.ne_iff.mp
      (Weight.coe_toLinear_ne_zero_iff.mpr (H.isNonZero_coe_root α))
  exact ⟨h, fun α hα ↦ hh ⟨α, hα⟩⟩

end LieSubalgebra

namespace LieModuleHom

open LieModule

section Injective

variable {R L M N S : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [SetLike S (Module.Dual R L)]

/-- **A module embedding in one whose weights lie in a set has its weights in that set.** Every
weight of `M` is a weight of `N` when `M` maps injectively and equivariantly to `N`, so if each
weight of `N` agrees with a linear form in `s`, such as an element of a weight lattice, then so
does each weight of `M`. In particular this applies to the Lie submodules of `N`. -/
theorem exists_mem_weight_of_injective {s : S} (f : M →ₗ⁅R,L⁆ N) (hf : Function.Injective f)
    (hN : ∀ χ : Weight R L N, ∃ φ ∈ s, ⇑φ = ⇑χ) (χ : Weight R L M) : ∃ φ ∈ s, ⇑φ = ⇑χ := by
  obtain ⟨m, hm, hm₀⟩ := χ.exists_ne_zero
  refine hN ⟨χ, fun h ↦ hm₀ (hf ?_)⟩
  have hfm : f m ∈ genWeightSpace N (χ : L → R) :=
    map_genWeightSpace_le f (LieSubmodule.mem_map_of_mem hm)
  rw [h, LieSubmodule.mem_bot] at hfm
  rw [hfm, map_zero]

end Injective

end LieModuleHom
