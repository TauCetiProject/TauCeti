/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.LinearAlgebra.Dimension.Localization

/-!
# Exact sequences of group-algebra modules split over the field of fractions

Let `R` be a domain with field of fractions `Q` and let `G` be a finite group whose order is
nonzero in `R`. A short exact sequence `0 → M → N → P → 0` of `R[G]`-modules need not split, but
it does after tensoring with `Q`: this is Maschke's theorem for `Q[G]`. This file proves it in the
form used for integral representations, where the rationalizations are written `M ⊗[R] Q` and
remain modules over `R[G]` rather than over `Q[G]`.

When `N` is finitely generated and `P` is projective over `R`, the splitting is obtained without
dividing by the order of `G`. An `R`-linear section `s` of `N → P` averaged over `G`,
`t = ∑_g g⁻¹ s g`, is `R[G]`-linear and satisfies `g ∘ t = #G`. Since `P` is torsion-free, the map
`M × P → N`, `(m, x) ↦ f m + t x`, is then an injective `R[G]`-linear map between modules of the
same rank, and it becomes bijective over `Q`.

For `R = ℤ_p` and `Q = ℚ_p` this computes the rational representation of an extension of
`ℤ_p[G]`-lattices from those of its two ends.

## Main results

* `TauCeti.IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact`: for an exact sequence
  `0 → M → N → P → 0` of `R[G]`-modules with `N` finite and `P` projective over `R`, the
  rationalization `N ⊗[R] Q` is `R[G]`-linearly isomorphic to `(M × P) ⊗[R] Q`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §1.3 and §15.
-/

public section

namespace TauCeti.IsFractionRing

open scoped TensorProduct

variable {R : Type*} [CommRing R] [IsDomain R] (Q : Type*) [Field Q] [Algebra R Q]
  [IsFractionRing R Q] {G : Type*} [Group G] [Finite G]
  {M N P : Type*} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R G) M]
  [IsScalarTower R (MonoidAlgebra R G) M]
  [AddCommGroup N] [Module R N] [Module (MonoidAlgebra R G) N]
  [IsScalarTower R (MonoidAlgebra R G) N]
  [AddCommGroup P] [Module R P] [Module (MonoidAlgebra R G) P]
  [IsScalarTower R (MonoidAlgebra R G) P]

/-- **Short exact sequences of group-algebra modules split over the field of fractions.** Let `R`
be a domain with field of fractions `Q` and `G` a finite group whose order is nonzero in `R`. For
an exact sequence `0 → M → N → P → 0` of `R[G]`-modules with `N` finitely generated and `P`
projective over `R`, the rationalization `N ⊗[R] Q` is `R[G]`-linearly isomorphic to
`(M × P) ⊗[R] Q`. -/
theorem nonempty_tensor_linearEquiv_prod_of_exact [NeZero (Nat.card G : R)] [Module.Finite R N]
    [Module.Projective R P] {f : M →ₗ[MonoidAlgebra R G] N} {g : N →ₗ[MonoidAlgebra R G] P}
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Nonempty ((N ⊗[R] Q) ≃ₗ[MonoidAlgebra R G] ((M × P) ⊗[R] Q)) := by
  have := Fintype.ofFinite G
  -- An `R`-linear section `s` of `g`, which exists because `P` is projective over `R`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (g.restrictScalars R) LinearMap.id hg
  have hs' (x : P) : g (s x) = x := LinearMap.congr_fun hs x
  -- Averaging `s` over `G` gives an `R[G]`-linear map `t` with `g ∘ t = #G`.
  let t := s.sumOfConjugatesEquivariant G
  have ht (x : P) : g (t x) = (Nat.card G : R) • x := by
    rw [LinearMap.sumOfConjugatesEquivariant_apply, map_sum]
    simp only [LinearMap.conjugate_apply, map_smul, hs', smul_smul,
      MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul R]
    rw [← MonoidAlgebra.one_def, one_smul]
  -- So `(m, x) ↦ f m + t x` is injective, as `P` is torsion-free.
  let Φ : (M × P) →ₗ[MonoidAlgebra R G] N :=
    f ∘ₗ LinearMap.fst _ M P + t ∘ₗ LinearMap.snd _ M P
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨m, x⟩ h
    have hx : x = 0 := by
      have h' := congrArg g h
      simp only [Φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, map_add, ht, map_zero, hfg.apply_apply_eq_zero, zero_add] at h'
      exact (smul_eq_zero.mp h').resolve_left (NeZero.ne _)
    subst hx
    simp only [Φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, map_zero, add_zero] at h
    rw [hf (h.trans f.map_zero.symm)]
    rfl
  -- Over `R` the sequence splits, so `M × P` and `N` have the same rank.
  have hrank : Module.finrank R (M × P) = Module.finrank R N :=
    (Function.Exact.splitSurjectiveEquiv (f := f.restrictScalars R) (g := g.restrictScalars R)
      hfg hf ⟨s, hs⟩).1.finrank_eq.symm
  exact ⟨(LinearEquiv.ofBijective _
    (rTensor_bijective_of_injective_of_finrank_eq Q Φ hΦ hrank)).symm⟩

end TauCeti.IsFractionRing
