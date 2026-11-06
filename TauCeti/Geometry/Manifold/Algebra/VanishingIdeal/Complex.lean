/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Complex algebraic cotangent spaces of real manifolds

At an interior point of a finite-dimensional Hausdorff real manifold, the ideal of
complex-valued smooth functions vanishing there has square exactly the functions with zero
value and zero differential. Its algebraic cotangent space is therefore the space of
complex-valued real-linear covectors, with its natural complex scalar action.
These are real-smooth functions, not holomorphic functions.

The square-ideal calculation reduces to real and imaginary parts and the real Hadamard
factorization in `TauCeti.mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint`.
The quotient and its descent use Mathlib's
`Ideal.Cotangent` and `Ideal.Cotangent.lift`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The ideal of complex-valued real-smooth functions vanishing at a point. -/
def complexSmoothVanishingIdeal (x : M) : Ideal C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  RingHom.ker (ContMDiffMap.evalRingHom x)

variable {I}

/-- Membership in the complex vanishing ideal is pointwise vanishing. -/
@[simp]
theorem mem_complexSmoothVanishingIdeal_iff {x : M} {f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    f ∈ complexSmoothVanishingIdeal I x ↔ f x = 0 :=
  RingHom.mem_ker

/-- Inclusion of real functions sends the square of the real vanishing ideal into the complex
square ideal. -/
theorem ofReal_mem_complexSmoothVanishingIdeal_sq {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I x ^ 2) :
    ContMDiffMap.ofReal f ∈ complexSmoothVanishingIdeal I x ^ 2 := by
  have hmap : Ideal.map (ContMDiffMap.ofReal (I := I) (M := M) (n := ∞))
      (smoothVanishingIdeal I x) ≤ complexSmoothVanishingIdeal I x := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    simpa using mem_smoothVanishingIdeal_iff.mp hg
  apply pow_le_pow_left' hmap 2
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem ContMDiffMap.ofReal hf

/-- A complex smooth function is in the square ideal exactly when both its real and imaginary
parts are in the corresponding real square ideal. -/
theorem mem_complexSmoothVanishingIdeal_sq_iff_re_im {x : M}
    (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    f ∈ complexSmoothVanishingIdeal I x ^ 2 ↔
      f.re ∈ smoothVanishingIdeal I x ^ 2 ∧ f.im ∈ smoothVanishingIdeal I x ^ 2 := by
  constructor
  · intro hf
    rw [sq] at hf
    refine Submodule.mul_induction_on hf (fun g hg h hh ↦ ?_) (fun g h hg hh ↦ ?_)
    · have hgr : g.re ∈ smoothVanishingIdeal I x := by simp_all
      have hgi : g.im ∈ smoothVanishingIdeal I x := by simp_all
      have hhr : h.re ∈ smoothVanishingIdeal I x := by simp_all
      have hhi : h.im ∈ smoothVanishingIdeal I x := by simp_all
      simp only [ContMDiffMap.mul_re, ContMDiffMap.mul_im, sq]
      exact ⟨sub_mem (Ideal.mul_mem_mul hgr hhr) (Ideal.mul_mem_mul hgi hhi),
        add_mem (Ideal.mul_mem_mul hgr hhi) (Ideal.mul_mem_mul hgi hhr)⟩
    · simpa using And.intro (add_mem hg.1 hh.1) (add_mem hg.2 hh.2)
  · rintro ⟨hr, hi⟩
    rw [← f.ofReal_re_add_I_smul_im]
    exact add_mem (ofReal_mem_complexSmoothVanishingIdeal_sq hr)
      (Submodule.smul_of_tower_mem _ Complex.I (ofReal_mem_complexSmoothVanishingIdeal_sq hi))

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- At an interior point the complex square ideal is the kernel of value and differential. -/
theorem mem_complexSmoothVanishingIdeal_sq_iff_of_isInteriorPoint {x : M}
    (hx : I.IsInteriorPoint x) (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    f ∈ complexSmoothVanishingIdeal I x ^ 2 ↔ f x = 0 ∧ mvfderiv I f x = 0 := by
  rw [mem_complexSmoothVanishingIdeal_sq_iff_re_im,
    mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint hx,
    mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint hx,
    ← mvfderiv_eq_zero_iff, ← mvfderiv_eq_zero_iff,
    ContMDiffMap.mvfderiv_eq_zero_iff_re_im f (by simp)]
  simp only [ContMDiffMap.re_apply, ContMDiffMap.im_apply, Complex.ext_iff,
    Complex.zero_re, Complex.zero_im]
  tauto

/-- On a boundaryless manifold the complex square ideal consists of the functions with zero
value and zero differential. -/
theorem mem_complexSmoothVanishingIdeal_sq_iff [BoundarylessManifold I M] (x : M)
    (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    f ∈ complexSmoothVanishingIdeal I x ^ 2 ↔ f x = 0 ∧ mvfderiv I f x = 0 :=
  mem_complexSmoothVanishingIdeal_sq_iff_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint f

private def complexVanishingIdealDifferential (x : M) :
    complexSmoothVanishingIdeal I x →ₗ[ℂ] (TangentSpace I x →L[ℝ] ℂ) where
  toFun f := mvfderiv I (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x
  map_add' f g := by
    rw [Submodule.coe_add, ContMDiffMap.coe_add,
      mvfderiv_add ((f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).contMDiff.mdifferentiable
        (by simp)).mdifferentiableAt
        ((g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).contMDiff.mdifferentiable
        (by simp)).mdifferentiableAt]
  map_smul' c f := by
    rw [Submodule.coe_smul_of_tower, RingHom.id_apply]
    have hcoe : ⇑(c • (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)) =
        fun y ↦ c • (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) y := by
      funext y
      exact ContMDiffMap.complex_smul_apply c _ y
    rw [hcoe]
    exact mvfderiv_const_smul
      ((f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).contMDiff.mdifferentiable
        (by simp)).mdifferentiableAt c

private theorem complexVanishingIdealDifferential_mul {x : M} (hx : I.IsInteriorPoint x)
    (f g : complexSmoothVanishingIdeal I x) :
    complexVanishingIdealDifferential (I := I) x (f * g) = 0 :=
  ((mem_complexSmoothVanishingIdeal_sq_iff_of_isInteriorPoint hx _).mp
    (sq (complexSmoothVanishingIdeal I x) ▸ Ideal.mul_mem_mul f.2 g.2)).2

/-- The complex algebraic cotangent space of a real manifold is the space of complex-valued
real-linear covectors. The equivalence sends the class of a function to its differential. -/
def complexSmoothCotangentEquiv {x : M} (hx : I.IsInteriorPoint x) :
    (complexSmoothVanishingIdeal I x).Cotangent ≃ₗ[ℂ] (TangentSpace I x →L[ℝ] ℂ) :=
  LinearEquiv.ofBijective
    (Ideal.Cotangent.lift (complexVanishingIdealDifferential (I := I) x)
      (complexVanishingIdealDifferential_mul hx))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro u hu
      obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ u
      rw [Ideal.Cotangent.lift_toCotangent] at hu
      rw [Ideal.toCotangent_eq_zero,
        mem_complexSmoothVanishingIdeal_sq_iff_of_isInteriorPoint hx]
      exact ⟨mem_complexSmoothVanishingIdeal_iff.mp f.2, hu⟩,
    fun L ↦ by
      obtain ⟨f, hf, -, -, hf₀, hf₁⟩ :=
        exists_contMDiff_hasCompactSupport_mvfderiv_eq (I := I) x (0 : ℂ) L Filter.univ_mem
      refine ⟨(complexSmoothVanishingIdeal I x).toCotangent
        ⟨⟨f, hf⟩, mem_complexSmoothVanishingIdeal_iff.mpr hf₀⟩, ?_⟩
      rw [Ideal.Cotangent.lift_toCotangent]
      exact hf₁⟩

/-- The class of a vanishing complex function corresponds to its actual differential. -/
@[simp]
theorem complexSmoothCotangentEquiv_toCotangent {x : M} (hx : I.IsInteriorPoint x)
    (f : complexSmoothVanishingIdeal I x) :
    complexSmoothCotangentEquiv hx ((complexSmoothVanishingIdeal I x).toCotangent f) =
      mvfderiv I (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x :=
  Ideal.Cotangent.lift_toCotangent _ (complexVanishingIdealDifferential_mul hx) f

end TauCeti
