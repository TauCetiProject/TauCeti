/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Closed points of projective space

Let `N` be a finite-dimensional vector space over an algebraically closed field `k`, the space
of linear homogeneous coordinates of `Proj (Sym N)`. Every closed point of `Proj (Sym N)` is
rational: in positive degrees, its homogeneous prime ideal consists of the polynomials that
vanish at a nonzero functional `v : N →ₗ[k] k`. For `N = V∨` such a functional is evaluation at
a nonzero vector of `V`, so the closed points of the projective space of lines in `V` are lines.

The point is read on the standard chart `D₊(φ)` of a linear coordinate `φ` not vanishing at it.
This chart is the spectrum of a finitely generated `k`-algebra, so by the Nullstellensatz the
point is the kernel of a `k`-algebra homomorphism `ψ` on it
(`PrimeSpectrum.exists_kernelPoint_eq_of_isClosed`); the functional is `c ↦ ψ (c / φ)`, and
`ψ` evaluates every homogeneous fraction `a / φⁿ` as `a` at this functional.

## Main declarations

* `TauCeti.SymmetricAlgebra.apply_awayMk_eq_lift`: a `k`-algebra homomorphism on the chart of a
  linear coordinate `φ` evaluates `a / φⁿ` as `a` at the functional `c ↦ ψ (c / φ)`.
* `ProjectiveSpectrum.exists_ne_zero_forall_mem_symmetricAlgebra_iff_of_isClosed`: a closed
  point of `Proj (Sym N)` is the vanishing locus of a nonzero functional on `N`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition II.2.6: the closed
  points of the scheme of a variety over an algebraically closed field are its points.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace TauCeti.SymmetricAlgebra

universe u

section Chart

variable {k N A : Type u} [CommRing k] [AddCommMonoid N] [Module k N] [CommRing A] [Algebra k A]

/-- On the standard chart `D₊(φ)` of a linear coordinate `φ`, a `k`-algebra homomorphism `ψ`
evaluates a homogeneous fraction `a / φⁿ` as the polynomial `a` evaluated at a linear map `v`
that agrees with `c ↦ ψ (c / φ)` on linear coordinates. -/
theorem apply_awayMk_eq_lift {φ : N}
    (ψ : Away (homogeneousSubmodule k N) (SymmetricAlgebra.ι k N φ) →ₐ[k] A) (v : N →ₗ[k] A)
    (hv : ∀ c, ψ (Away.mk _ (ι_mem_homogeneousSubmodule k N φ) 1 (SymmetricAlgebra.ι k N c)
      (by simp)) = v c)
    {n : ℕ} {a : SymmetricAlgebra k N} (ha : a ∈ homogeneousSubmodule k N n) :
    ψ (Away.mk _ (ι_mem_homogeneousSubmodule k N φ) n a (by rwa [smul_eq_mul, mul_one])) =
      SymmetricAlgebra.lift v a := by
  have hφ := ι_mem_homogeneousSubmodule k N φ
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    have : Away.mk _ hφ 0 (algebraMap k _ r) (by simp) = algebraMap k (Away _ _) r := by
      apply val_injective
      rw [Away.val_mk, val_algebraMap,
        IsScalarTower.algebraMap_apply k (SymmetricAlgebra k N) (Localization.Away _) r,
        ← Localization.mk_one_eq_algebraMap]
      exact congrArg _ (Subtype.ext (pow_zero _))
    rw [this]
    simp
  | add a b i ha hb iha ihb =>
    have : Away.mk _ hφ i (a + b) (by simpa using add_mem ha hb) =
        Away.mk _ hφ i a (by simpa using ha) + Away.mk _ hφ i b (by simpa using hb) := by
      apply val_injective
      simp [Away.val_mk, Localization.add_mk_self]
    rw [this, map_add, iha, ihb, map_add]
  | mem_mul c hc i a ha iha =>
    obtain ⟨c, rfl⟩ := hc
    have hc : SymmetricAlgebra.ι k N c ∈ homogeneousSubmodule k N (1 • 1) := by simp
    have ha' : a ∈ homogeneousSubmodule k N (i • 1) := by simpa using ha
    have hca : SymmetricAlgebra.ι k N c * a ∈ homogeneousSubmodule k N ((i + 1) • 1) := by
      simpa [add_comm] using SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule k N c) ha
    have : Away.mk _ hφ (i + 1) _ hca = Away.mk _ hφ 1 _ hc * Away.mk _ hφ i a ha' := by
      apply val_injective
      simp [Away.val_mk, Localization.mk_mul, pow_succ']
    rw [this, map_mul, iha, map_mul, SymmetricAlgebra.lift_ι_apply, hv]

end Chart

end TauCeti.SymmetricAlgebra

namespace ProjectiveSpectrum

open TauCeti.SymmetricAlgebra

universe u

variable {k N : Type u} [Field k] [AddCommGroup N] [Module k N]

/-- Over an algebraically closed field, a closed point of the projective spectrum of `Sym N`, for
`N` finite-dimensional, is cut out by a nonzero functional `v` on `N`: a homogeneous polynomial
of positive degree lies in its homogeneous prime ideal exactly when it vanishes at `v`. -/
theorem exists_ne_zero_forall_mem_symmetricAlgebra_iff_of_isClosed [IsAlgClosed k]
    [Module.Finite k N] (x : Proj (homogeneousSubmodule k N)) (hx : IsClosed {x}) :
    ∃ v : Module.Dual k N, v ≠ 0 ∧ ∀ n > 0, ∀ s ∈ homogeneousSubmodule k N n,
      s ∈ x.asHomogeneousIdeal ↔ SymmetricAlgebra.lift v s = 0 := by
  -- A relevant prime does not contain every linear coordinate.
  obtain ⟨φ, hφx⟩ : ∃ φ : N, SymmetricAlgebra.ι k N φ ∉ x.asHomogeneousIdeal := by
    by_contra! h
    refine x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le _).mpr fun n hn t ht ↦ ?_)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    rw [homogeneousSubmodule, pow_succ'] at ht
    refine (Submodule.mul_le (P := x.asHomogeneousIdeal.toIdeal.restrictScalars k)).mpr
      (fun a ha b _ ↦ ?_) ht
    obtain ⟨c, rfl⟩ := ha
    exact Ideal.mul_mem_right b _ (h c)
  have hφ := ι_mem_homogeneousSubmodule k N φ
  obtain ⟨y, rfl⟩ : x ∈ Set.range (Proj.awayι _ _ hφ one_pos) := by
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    exact hφx
  -- The chart is a finitely generated `k`-algebra, so its closed points are rational.
  have : Algebra.FiniteType k (Away (homogeneousSubmodule k N) (SymmetricAlgebra.ι k N φ)) := by
    have : LocallyOfFiniteType (Proj.awayι _ _ hφ one_pos ≫ projToSpec k N) := inferInstance
    rw [awayι_projToSpec] at this
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  have hy : IsClosed {y} := by
    rw [← (Proj.awayι _ _ hφ one_pos).isOpenEmbedding.injective.preimage_image {y},
      Set.image_singleton]
    exact hx.preimage (Proj.awayι _ _ hφ one_pos).continuous
  obtain ⟨ψ, rfl⟩ := PrimeSpectrum.exists_kernelPoint_eq_of_isClosed (k := k) y hy
  -- The point is given by the functional `c ↦ ψ (c / φ)` on linear coordinates.
  let v : Module.Dual k N := ψ.toLinearMap ∘ₗ Away.mkLinearMap hφ 1 ∘ₗ
    (SymmetricAlgebra.ι k N).codRestrict (homogeneousSubmodule k N (1 • 1))
      (fun c ↦ by simp)
  have key {n : ℕ} {a : SymmetricAlgebra k N} (ha : a ∈ homogeneousSubmodule k N n) :=
    apply_awayMk_eq_lift ψ v (fun c ↦ by simp [v]) ha
  refine ⟨v, fun hv ↦ ?_, fun n hn s hs ↦ ?_⟩
  · -- The functional takes the value `1` on the chart coordinate `φ`.
    have h1 : Away.mk _ hφ 1 (SymmetricAlgebra.ι k N φ) (by simp) = 1 := by
      apply val_injective
      simp [Away.val_mk]
    have := key hφ
    rw [h1, map_one, SymmetricAlgebra.lift_ι_apply, hv, LinearMap.zero_apply] at this
    exact one_ne_zero this
  · -- Read membership in `x` on the chart, where `s` becomes `s / φⁿ`.
    rw [← not_iff_not, ← Proj.mem_basicOpen, ← Scheme.Hom.mem_preimage,
      Proj.awayι_preimage_basicOpen _ hφ one_pos hs hn]
    -- The open is `PrimeSpectrum.basicOpen` viewed as an open of the scheme `Spec`, whose type
    -- differs syntactically from the opens of `PrimeSpectrum`, so `PrimeSpectrum.mem_basicOpen`
    -- is applied by unification rather than by rewriting.
    refine (PrimeSpectrum.mem_basicOpen (Away.isLocalizationElem hφ hs) _).trans ?_
    rw [TauCeti.AlgHom.kernelPoint_asIdeal, RingHom.mem_ker]
    have := key (n := n) (a := s ^ 1) (by simpa using hs)
    rw [map_pow, pow_one (SymmetricAlgebra.lift v s)] at this
    exact not_congr (Iff.of_eq (congrArg (· = (0 : k)) this))

end ProjectiveSpectrum
