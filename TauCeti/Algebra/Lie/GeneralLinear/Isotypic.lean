/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Carrier
public import TauCeti.Algebra.Lie.Isotypic
public import TauCeti.Algebra.Lie.Multiplicity
-- Non-public: these declarations appear only inside proofs.
import TauCeti.Algebra.Lie.GeneralLinear.Existence
import TauCeti.Algebra.Lie.UniversalEnveloping.Multiplicity

/-!
# The single-weight isotypy criterion for `gl_n`

This file packages highest-weight existence and uniqueness into isotypy criteria for modules over
the general linear Lie algebra. If every irreducible submodule has the same highest weight, then
every pair of irreducible submodules is equivalent. Under complete reducibility, the module is the
direct sum of copies of the named irreducible with that weight when the module is nonzero. For the
zero module, the result is the empty direct sum and makes no dominance or irreducibility claim
about the named carrier. Under complete reducibility a highest weight vector also generates an
irreducible submodule, which is a copy of the named irreducible of its weight.

The foundational `LieModule.IsIsotypic` assertion is pairwise. The counted direct-sum theorem adds
complete reducibility explicitly, since it is not automatic for representations of a reductive Lie
algebra unless its centre acts semisimply.

## Main results

* `isIsotypic_of_forall_irreducible_exists_isGlHighestWeightVector`: a criterion using a supplied
  highest-weight vector in every irreducible submodule.
* `isIsotypicOfType_of_forall_irreducible_exists_isGlHighestWeightVector`: the supplied-vector
  criterion identifying an arbitrary irreducible type.
* `isIsotypic_of_forall_isGlHighestWeightVector`: the finite-dimensional criterion over an
  algebraically closed field.
* `isIsotypicOfType_of_forall_isGlHighestWeightVector`: the criterion identifying an arbitrary
  irreducible type from one highest-weight vector.
* `isGlDominantIntegral_of_forall_isGlHighestWeightVector`: the dominance consequence of the
  finite-dimensional single-weight hypothesis for a nonzero module.
* `LieSubmodule.exists_isGlHighestWeightVector_of_forall`: the highest-weight existence criterion
  for a nonzero submodule.
* `isIsotypicOfType_glIrreducible_of_forall_isGlHighestWeightVector`: the fixed-carrier criterion.
* `nonempty_lieModuleEquiv_directSum_glIrreducible_of_forall_isGlHighestWeightVector`: the counted
  direct-sum criterion for a completely reducible module.
* `isIrreducible_lieSpan_of_isGlHighestWeightVector`: in a completely reducible module a highest
  weight vector generates an irreducible submodule.
* `exists_lieModuleHom_glIrreducible_apply_eq`: in a completely reducible module every highest
  weight vector of dominant weight `ν` is the image of the generator of `glIrreducible N ν`.

## References

The formal precedent is `TauCeti.isIsotypicOfType_of_forall_isHighestWeightVector` in
`TauCeti/Algebra/Lie/HighestWeight/Isotypic.lean`.
-/

public section

namespace TauCeti

open _root_.LieModule Matrix
open scoped DirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

variable {K : Type u} [Field K] [CharZero K]
variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
variable {M : Type v} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix n n K) M]
  [LieModule K (Matrix n n K) M]
variable {S : Type w} [AddCommGroup S] [Module K S]
  [LieRingModule (Matrix n n K) S]
  [LieModule K (Matrix n n K) S]
variable {mu : n → K}

/-- If every irreducible submodule of a `gl_n`-module carries a highest-weight vector of weight
`mu`, and an irreducible module `S` carries one too, then the original module is isotypic of type
`S`.

This supplied-vector form does not require finite-dimensionality or an algebraically closed
field. -/
theorem isIsotypicOfType_of_forall_irreducible_exists_isGlHighestWeightVector
    [_root_.LieModule.IsIrreducible K (Matrix n n K) S]
    {w : S} (hw : IsGlHighestWeightVector mu w)
    (h : ∀ (P : LieSubmodule K (Matrix n n K) M)
      [_root_.LieModule.IsIrreducible K (Matrix n n K) P],
      ∃ v : P, IsGlHighestWeightVector mu v) :
    _root_.LieModule.IsIsotypicOfType K (Matrix n n K) M S := by
  rw [_root_.LieModule.isIsotypicOfType_iff]
  intro P _
  obtain ⟨v, hv⟩ := h P
  exact nonempty_lieModuleEquiv_of_isGlHighestWeightVector hv hw

/-- If every irreducible submodule of a `gl_n`-module carries a highest-weight vector of weight
`mu`, then the module is isotypic.

This form does not require finite-dimensionality or an algebraically closed field: those
hypotheses are only needed to produce the highest-weight vectors, which are supplied here. -/
theorem isIsotypic_of_forall_irreducible_exists_isGlHighestWeightVector
    (h : ∀ (P : LieSubmodule K (Matrix n n K) M)
      [_root_.LieModule.IsIrreducible K (Matrix n n K) P],
      ∃ v : P, IsGlHighestWeightVector mu v) :
    _root_.LieModule.IsIsotypic K (Matrix n n K) M := by
  rw [_root_.LieModule.isIsotypic_iff]
  intro P _
  obtain ⟨v, hv⟩ := h P
  exact isIsotypicOfType_of_forall_irreducible_exists_isGlHighestWeightVector hv h

/-- **In a completely reducible `gl_n`-module a highest weight vector generates an irreducible
submodule.** If a proper nonzero submodule `P` of the module `v` generates had a complement `Q`,
the `P`-component of `v` would be a vector of the weight of `v` in that module, hence a multiple of
`v`; either `v ∈ P`, or `v ∈ Q` and `P ≤ P ⊓ Q = ⊥`. -/
theorem isIrreducible_lieSpan_of_isGlHighestWeightVector
    [ComplementedLattice (LieSubmodule K (Matrix n n K) M)] {v : M}
    (hv : IsGlHighestWeightVector mu v) :
    _root_.LieModule.IsIrreducible K (Matrix n n K)
      (LieSubmodule.lieSpan K (Matrix n n K) {v}) := by
  have hvmem : v ∈ LieSubmodule.lieSpan K (Matrix n n K) {v} := LieSubmodule.subset_lieSpan rfl
  rw [isIrreducible_iff_isAtom]
  refine ⟨fun h => hv.ne_zero (by simpa [h] using hvmem), fun P hP => ?_⟩
  obtain ⟨Q, hPQ⟩ := exists_isCompl P
  have hinf (m : M) (hmP : m ∈ P) (hmQ : m ∈ Q) : m = 0 := by
    have hm : m ∈ P ⊓ Q := (LieSubmodule.mem_inf _ _ m).mpr ⟨hmP, hmQ⟩
    rwa [hPQ.inf_eq_bot, LieSubmodule.mem_bot] at hm
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (LieSubmodule.mem_sup _ _ v).mp (hPQ.sup_eq_top ▸ LieSubmodule.mem_top v)
  have hpw (i : n) : ⁅(single i i (1 : K) : Matrix n n K), p⁆ = mu i • p := by
    have hsum := hv.lie_single_self_eq_smul i
    rw [← hpq, lie_add, smul_add] at hsum
    have hdiff : ⁅(single i i (1 : K) : Matrix n n K), p⁆ - mu i • p =
        mu i • q - ⁅(single i i (1 : K) : Matrix n n K), q⁆ := by
      rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
    exact sub_eq_zero.mp (hinf _ (sub_mem (P.lie_mem hp) (P.smul_mem _ hp))
      (hdiff ▸ sub_mem (Q.smul_mem _ hq) (Q.lie_mem hq)))
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isGlHighestWeightVector_of_mem_lieSpan hv (hP.le hp) hpw
  by_cases hc0 : c = 0
  · have hvQ : LieSubmodule.lieSpan K (Matrix n n K) {v} ≤ Q := by
      rw [LieSubmodule.lieSpan_le, Set.singleton_subset_iff, ← hpq, hc, hc0, zero_smul, zero_add]
      exact hq
    exact eq_bot_iff.mpr fun m hm => (hinf m hm (hvQ (hP.le hm))) ▸ LieSubmodule.zero_mem _
  · have hvP : LieSubmodule.lieSpan K (Matrix n n K) {v} ≤ P := by
      rw [LieSubmodule.lieSpan_le, Set.singleton_subset_iff]
      have hvp : v = c⁻¹ • p := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hvp]
      exact P.smul_mem _ hp
    exact absurd (le_antisymm hP.le hvP) hP.ne

section Fin

variable {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M]
  [LieModule K (Matrix (Fin N) (Fin N) K) M]
variable {S : Type w} [AddCommGroup S] [Module K S]
  [LieRingModule (Matrix (Fin N) (Fin N) K) S]
  [LieModule K (Matrix (Fin N) (Fin N) K) S]
variable {mu : Fin N → K}

/-- Every nonzero finite-dimensional submodule of a `gl_N`-module over an algebraically closed field
contains a highest-weight vector of weight `mu`, when all highest-weight vectors in that submodule
have that weight. -/
theorem _root_.LieSubmodule.exists_isGlHighestWeightVector_of_forall
    [IsAlgClosed K]
    (P : LieSubmodule K (Matrix (Fin N) (Fin N) K) M) [FiniteDimensional K P]
    (hP : P ≠ ⊥)
    (h : ∀ (nu : Fin N → K) (v : P),
      TauCeti.IsGlHighestWeightVector nu v → nu = mu) :
    ∃ v : P, TauCeti.IsGlHighestWeightVector mu v := by
  let _ : Nontrivial P := (LieSubmodule.nontrivial_iff_ne_bot K
    (Matrix (Fin N) (Fin N) K) M).mpr hP
  obtain ⟨nu, v, hv⟩ := TauCeti.exists_isGlHighestWeightVector
    (K := K) (n := Fin N) (M := P)
  have hnu : nu = mu := h nu v hv
  subst nu
  exact ⟨v, hv⟩

private theorem exists_isGlHighestWeightVector_irreducible_of_forall
    [IsAlgClosed K] [FiniteDimensional K M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    ∀ (P : LieSubmodule K (Matrix (Fin N) (Fin N) K) M)
      [_root_.LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) P],
      ∃ v : P, IsGlHighestWeightVector mu v := by
  intro P _
  exact LieSubmodule.exists_isGlHighestWeightVector_of_forall P
    ((LieSubmodule.nontrivial_iff_ne_bot K (Matrix (Fin N) (Fin N) K) M).mp
      (_root_.LieModule.nontrivial_of_isIrreducible
        (R := K) (L := Matrix (Fin N) (Fin N) K) (M := P)))
    (fun nu v hv => h nu (v : M) (isGlHighestWeightVector_coe_iff.mpr hv))

/-- **The single-weight isotypy criterion for `gl_N`.** If every highest-weight vector in a
finite-dimensional `gl_N`-module over an algebraically closed field has weight `mu`, then every
pair of irreducible submodules is equivalent. -/
theorem isIsotypic_of_forall_isGlHighestWeightVector [IsAlgClosed K] [FiniteDimensional K M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    _root_.LieModule.IsIsotypic K (Matrix (Fin N) (Fin N) K) M :=
  isIsotypic_of_forall_irreducible_exists_isGlHighestWeightVector
    (exists_isGlHighestWeightVector_irreducible_of_forall h)

/-- If an irreducible `gl_N`-module `S` carries a highest-weight vector of weight `mu`, then a
finite-dimensional module over an algebraically closed field whose highest-weight vectors all have
weight `mu` is isotypic of type `S`. -/
theorem isIsotypicOfType_of_forall_isGlHighestWeightVector
    [IsAlgClosed K] [FiniteDimensional K M]
    [_root_.LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) S]
    {w : S} (hw : IsGlHighestWeightVector mu w)
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    _root_.LieModule.IsIsotypicOfType K (Matrix (Fin N) (Fin N) K) M S :=
  isIsotypicOfType_of_forall_irreducible_exists_isGlHighestWeightVector hw
    (exists_isGlHighestWeightVector_irreducible_of_forall h)

/-- If all highest-weight vectors in a nonzero finite-dimensional `gl_N`-module over an
algebraically closed field have weight `mu`, then `mu` is dominant integral. -/
theorem isGlDominantIntegral_of_forall_isGlHighestWeightVector
    [IsAlgClosed K] [FiniteDimensional K M] [Nontrivial M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    IsGlDominantIntegral mu := by
  obtain ⟨nu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (n := Fin N) (M := M)
  exact h nu v hv ▸ hv.isGlDominantIntegral

/-- **The single-weight fixed-carrier criterion for `gl_N`.** A finite-dimensional module over an
algebraically closed field whose highest-weight vectors all have weight `mu` is isotypic of type
`glIrreducible N mu`. For the zero module this holds vacuously. -/
theorem isIsotypicOfType_glIrreducible_of_forall_isGlHighestWeightVector
    [IsAlgClosed K] [FiniteDimensional K M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    _root_.LieModule.IsIsotypicOfType K (Matrix (Fin N) (Fin N) K) M
      (glIrreducible N mu) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · let _ := hM
    rw [_root_.LieModule.isIsotypicOfType_iff]
    intro P _
    exact (not_nontrivial P
      (_root_.LieModule.nontrivial_of_isIrreducible
        (R := K) (L := Matrix (Fin N) (Fin N) K) (M := P))).elim
  have hmu := isGlDominantIntegral_of_forall_isGlHighestWeightVector h
  let _ := isIrreducible_glIrreducible (K := K) hmu
  exact isIsotypicOfType_of_forall_isGlHighestWeightVector
    (isGlHighestWeightVector_glIrreducibleGenerator hmu) h

/-- **The single-weight direct-sum criterion for `gl_N`.** A finite-dimensional completely
reducible `gl_N`-module over an algebraically closed field whose highest-weight vectors all have
weight `mu` is the direct sum of
`LieModule.isotypicMultiplicity` copies of the named irreducible `glIrreducible N mu`.

Complete reducibility is an explicit hypothesis: it is not automatic for a reductive Lie algebra,
whose centre may act non-semisimply. For a nonzero module the weight is dominant integral, so the
named carrier is irreducible. For the zero module the multiplicity is zero, and the theorem only
identifies the empty direct sum without making a claim about the carrier. -/
theorem nonempty_lieModuleEquiv_directSum_glIrreducible_of_forall_isGlHighestWeightVector
    [IsAlgClosed K] [FiniteDimensional K M]
    [ComplementedLattice (LieSubmodule K (Matrix (Fin N) (Fin N) K) M)]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    Nonempty (M ≃ₗ⁅K,Matrix (Fin N) (Fin N) K⁆
      (⨁ (_ : Fin (_root_.LieModule.isotypicMultiplicity K (Matrix (Fin N) (Fin N) K) M
        (glIrreducible N mu))), glIrreducible N mu)) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · let _ := hM
    rw [_root_.LieModule.isotypicMultiplicity_eq_zero_of_subsingleton_codomain]
    let f : M →ₗ⁅K,Matrix (Fin N) (Fin N) K⁆ (⨁ (_ : Fin 0), glIrreducible N mu) := 0
    exact ⟨LieModuleEquiv.ofBijective f
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩⟩
  have hmu := isGlDominantIntegral_of_forall_isGlHighestWeightVector h
  let _ := isIrreducible_glIrreducible (K := K) hmu
  exact _root_.LieModule.nonempty_lieModuleEquiv_of_isIsotypicOfType _
    (isIsotypicOfType_glIrreducible_of_forall_isGlHighestWeightVector h)

/-- **In a completely reducible module every highest weight vector of dominant weight `ν` is
the image of the generator of `L(ν)`** under a morphism of `gl_N`-modules: the vector generates an
irreducible submodule (`TauCeti.isIrreducible_lieSpan_of_isGlHighestWeightVector`), which is `L(ν)`
with the vector matching the generator. -/
theorem exists_lieModuleHom_glIrreducible_apply_eq
    [ComplementedLattice (LieSubmodule K (Matrix (Fin N) (Fin N) K) M)] {nu : Fin N → K}
    (hnu : IsGlDominantIntegral nu) {v : M} (hv : IsGlHighestWeightVector nu v) :
    ∃ φ : glIrreducible N nu →ₗ⁅K,Matrix (Fin N) (Fin N) K⁆ M,
      φ (glIrreducibleGenerator N nu) = v := by
  let S := LieSubmodule.lieSpan K (Matrix (Fin N) (Fin N) K) {v}
  let _ := isIrreducible_lieSpan_of_isGlHighestWeightVector hv
  let _ := isIrreducible_glIrreducible (K := K) hnu
  let v' : S := ⟨v, LieSubmodule.subset_lieSpan rfl⟩
  have hv' : IsGlHighestWeightVector nu v' := isGlHighestWeightVector_coe_iff.mp hv
  let e := lieModuleEquivOfIsGlHighestWeightVector
    (isGlHighestWeightVector_glIrreducibleGenerator hnu) hv'
  refine ⟨S.incl.comp (e : glIrreducible N nu →ₗ⁅K,Matrix (Fin N) (Fin N) K⁆ S), ?_⟩
  simp [e, v']

end Fin

end TauCeti
