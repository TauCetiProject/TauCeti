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
about the named carrier.

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
* `isIsotypicOfType_glIrreducible_of_forall_isGlHighestWeightVector`: the fixed-carrier criterion.
* `nonempty_lieModuleEquiv_directSum_glIrreducible_of_forall_isGlHighestWeightVector`: the counted
  direct-sum criterion for a completely reducible module.

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

section Fin

variable {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M]
  [LieModule K (Matrix (Fin N) (Fin N) K) M]
variable {S : Type w} [AddCommGroup S] [Module K S]
  [LieRingModule (Matrix (Fin N) (Fin N) K) S]
  [LieModule K (Matrix (Fin N) (Fin N) K) S]
variable {mu : Fin N → K}

private theorem exists_submodule_isGlHighestWeightVector_of_forall
    [IsAlgClosed K] [FiniteDimensional K M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    ∀ (P : LieSubmodule K (Matrix (Fin N) (Fin N) K) M)
      [_root_.LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) P],
      ∃ v : P, IsGlHighestWeightVector mu v := by
  intro P _
  let _ : Nontrivial P :=
    _root_.LieModule.nontrivial_of_isIrreducible
      (R := K) (L := Matrix (Fin N) (Fin N) K) (M := P)
  obtain ⟨nu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (N := N) (M := P)
  have hnu : nu = mu := h nu (v : M) (isGlHighestWeightVector_coe_iff.mpr hv)
  subst nu
  exact ⟨v, hv⟩

/-- **The single-weight isotypy criterion for `gl_N`.** If every highest-weight vector in a
finite-dimensional `gl_N`-module over an algebraically closed field has weight `mu`, then every
pair of irreducible submodules is equivalent. -/
theorem isIsotypic_of_forall_isGlHighestWeightVector [IsAlgClosed K] [FiniteDimensional K M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    _root_.LieModule.IsIsotypic K (Matrix (Fin N) (Fin N) K) M :=
  isIsotypic_of_forall_irreducible_exists_isGlHighestWeightVector
    (exists_submodule_isGlHighestWeightVector_of_forall h)

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
    (exists_submodule_isGlHighestWeightVector_of_forall h)

/-- If all highest-weight vectors in a nonzero finite-dimensional `gl_N`-module over an
algebraically closed field have weight `mu`, then `mu` is dominant integral. -/
theorem isGlDominantIntegral_of_forall_isGlHighestWeightVector
    [IsAlgClosed K] [FiniteDimensional K M] [Nontrivial M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    IsGlDominantIntegral mu := by
  obtain ⟨nu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (N := N) (M := M)
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

end Fin

end TauCeti
