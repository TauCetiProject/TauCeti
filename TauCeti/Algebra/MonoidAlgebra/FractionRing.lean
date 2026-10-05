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
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Localization

/-!
# Exact sequences of group-algebra modules split over the field of fractions

Let `R` be a domain with field of fractions `Q` and let `G` be a finite group whose order is
nonzero in `R`. A short exact sequence `0 → M → N → P → 0` of `R[G]`-modules need not split, but
it does after tensoring with `Q`: this is Maschke's theorem for `Q[G]`. This file proves it in the
form used for integral representations, where the rationalizations are written `M ⊗[R] Q` and
remain modules over `R[G]` rather than over `Q[G]`.

No finiteness or projectivity is needed. Since `Q` is flat over `R`, the sequence stays exact
after tensoring with `Q`, and `P ⊗[R] Q` is a `Q`-vector space, so `N ⊗ Q → P ⊗ Q` has an
`R`-linear section `s`. Averaged over `G`, `t = ∑_g g⁻¹ s g` is `R[G]`-linear and satisfies
`g ∘ t = #G`. As `#G` is invertible on `P ⊗[R] Q`, the map `(m, x) ↦ f m + t x` from
`(M ⊗ Q) × (P ⊗ Q)` to `N ⊗ Q` is then an `R[G]`-linear bijection.

For `R = ℤ_p` and `Q = ℚ_p` this computes the rational representation of an extension of
`ℤ_p[G]`-lattices from those of its two ends.

## Main results

* `TauCeti.IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact`: for an exact sequence
  `0 → M → N → P → 0` of `R[G]`-modules, the rationalization `N ⊗[R] Q` is `R[G]`-linearly
  isomorphic to `(M × P) ⊗[R] Q`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §1.3 and §15.
-/

public section

namespace TauCeti.IsFractionRing

open scoped TensorProduct

variable {R : Type*} [CommRing R] (Q : Type*) [Field Q] [Algebra R Q]
  [IsFractionRing R Q] {G : Type*} [Group G] [Finite G]
  {M N P : Type*} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R G) M]
  [IsScalarTower R (MonoidAlgebra R G) M]
  [AddCommGroup N] [Module R N] [Module (MonoidAlgebra R G) N]
  [IsScalarTower R (MonoidAlgebra R G) N]
  [AddCommGroup P] [Module R P] [Module (MonoidAlgebra R G) P]
  [IsScalarTower R (MonoidAlgebra R G) P]

/-- **Short exact sequences of group-algebra modules split over the field of fractions.** Let `R`
be a domain with field of fractions `Q` and `G` a finite group whose order is nonzero in `R`. For
an exact sequence `0 → M → N → P → 0` of `R[G]`-modules, the rationalization `N ⊗[R] Q` is
`R[G]`-linearly isomorphic to `(M × P) ⊗[R] Q`. -/
theorem nonempty_tensor_linearEquiv_prod_of_exact [NeZero (Nat.card G : R)]
    {f : M →ₗ[MonoidAlgebra R G] N} {g : N →ₗ[MonoidAlgebra R G] P}
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Nonempty ((N ⊗[R] Q) ≃ₗ[MonoidAlgebra R G] ((M × P) ⊗[R] Q)) := by
  have := Fintype.ofFinite G
  -- `Q` is flat over `R`, so `0 → M ⊗ Q → N ⊗ Q → P ⊗ Q → 0` is exact.
  have := _root_.IsLocalization.flat Q (nonZeroDivisors R)
  set f' := TensorProduct.AlgebraTensorModule.rTensor R Q f
  set g' := TensorProduct.AlgebraTensorModule.rTensor R Q g
  have hf' : Function.Injective f' :=
    Module.Flat.rTensor_preserves_injective_linearMap (f.restrictScalars R) hf
  have hfg' : Function.Exact f' g' :=
    rTensor_exact Q (f := f.restrictScalars R) (g := g.restrictScalars R) hfg hg
  -- An `R`-linear section `s` of `g ⊗ 𝟙 Q`, from a `Q`-linear section of `𝟙 Q ⊗ g`.
  obtain ⟨s₀, hs₀⟩ := Module.projective_lifting_property
    (TensorProduct.AlgebraTensorModule.lTensor Q Q (g.restrictScalars R)) LinearMap.id
    (LinearMap.lTensor_surjective Q (g := g.restrictScalars R) hg)
  let s : P ⊗[R] Q →ₗ[R] N ⊗[R] Q := (TensorProduct.comm R Q N).toLinearMap ∘ₗ
    s₀.restrictScalars R ∘ₗ (TensorProduct.comm R P Q).toLinearMap
  have hs' (x : P ⊗[R] Q) : g' (s x) = x := by
    have hcomm (y : Q ⊗[R] N) : g' (TensorProduct.comm R Q N y) =
        TensorProduct.comm R Q P (TensorProduct.AlgebraTensorModule.lTensor Q Q
          (g.restrictScalars R) y) := by
      induction y using TensorProduct.inductionOn with
      | tmul q n => rfl
      | add y z hy hz => simp_all
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hcomm,
      LinearMap.restrictScalars_apply, ← LinearMap.comp_apply, hs₀, LinearMap.id_apply,
      LinearEquiv.coe_coe, TensorProduct.comm_comm]
  -- Averaging `s` over `G` gives an `R[G]`-linear map `t` with `g' ∘ t = #G`.
  let t := s.sumOfConjugatesEquivariant G
  have ht (x : P ⊗[R] Q) : g' (t x) = (Nat.card G : R) • x := by
    rw [LinearMap.sumOfConjugatesEquivariant_apply, map_sum]
    simp only [LinearMap.conjugate_apply, map_smul, hs', smul_smul,
      MonoidAlgebra.single_mul_single, inv_mul_cancel, one_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul R]
    rw [← MonoidAlgebra.one_def, one_smul]
  -- Multiplication by `#G` is invertible on `P ⊗ Q`.
  let u : P ⊗[R] Q →ₗ[R] P ⊗[R] Q :=
    (LinearMap.mulLeft R (algebraMap R Q (Nat.card G))⁻¹).lTensor P
  have hu (x : P ⊗[R] Q) : (Nat.card G : R) • u x = x := by
    have hc : algebraMap R Q (Nat.card G) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R Q)).mpr (NeZero.ne _)
    induction x using TensorProduct.inductionOn with
    | tmul p q =>
      rw [LinearMap.lTensor_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    | add x y hx hy => simp_all
  -- So `(m, x) ↦ f' m + t x` is bijective.
  let Φ : (M ⊗[R] Q) × (P ⊗[R] Q) →ₗ[MonoidAlgebra R G] N ⊗[R] Q :=
    f' ∘ₗ LinearMap.fst _ _ _ + t ∘ₗ LinearMap.snd _ _ _
  have hΦ : Function.Bijective Φ := by
    refine ⟨?_, fun n ↦ ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨m, x⟩ h
      have hx : x = 0 := by
        have h' := congrArg g' h
        simp only [Φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.snd_apply, map_add, ht, map_zero, hfg'.apply_apply_eq_zero, zero_add] at h'
        rw [← hu x, ← map_smul, h', map_zero]
      subst hx
      simp only [Φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, map_zero, add_zero] at h
      rw [hf' (h.trans f'.map_zero.symm)]
      rfl
    · obtain ⟨m, hm⟩ := (hfg' (n - t (u (g' n)))).mp (by rw [map_sub, ht, hu, sub_self])
      exact ⟨(m, u (g' n)), by simp [Φ, hm]⟩
  exact ⟨(LinearEquiv.ofBijective Φ hΦ).symm ≪≫ₗ (TensorProduct.prodLeft _ _ _ _ _).symm⟩

end TauCeti.IsFractionRing
