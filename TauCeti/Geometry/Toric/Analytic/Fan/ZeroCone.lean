/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Affine
public import TauCeti.Geometry.Toric.Analytic.Fan.Character
public import TauCeti.Geometry.Toric.Analytic.Fan.TorusAction.Holomorphic

/-!
# The analytic zero-cone fan is the complex torus

The canonical identification of the realization of the zero-cone fan with the coordinate-free
complex torus is a biholomorphism. Its forward map is the dense-torus inclusion. The inverse is
holomorphic because each torus coordinate is the global character function of the corresponding
integral character; every character is nonnegative on the zero cone.

The statement uses any finite free presentation of the character lattice. Thus the complex
structure on the torus and the analytic structure obtained by gluing the zero-cone fan agree
without a preferred integral basis.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.1 and 1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} {ι : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] [Fintype ι] {i : N →+ V} (hi : IsIntegralLattice i)
  (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

local notation "Φ₀" => ofCone hi (isToricCone_bot i)
local notation "h₀" => isRegular_ofCone hi (isRegularCone_bot hi)
local notation "z₀" => (Subtype.mk (⊥ : PointedCone ℝ V)
  (Iff.mpr (mem_ofCone_cones hi (isToricCone_bot i))
    (PointedCone.IsFaceOf.refl ⊥)) : Fan.cones Φ₀)

/-- The canonical torus inclusion in the realization of the zero-cone fan is holomorphic for
any finite free presentation of its character lattice. -/
theorem contMDiff_analyticZeroConeHomeomorph (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (analyticZeroConeHomeomorph hi) := by
  intro _
  let _ := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
  let hsmul : ContMDiffSMul 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (ComplexTorus N) ((ofCone hi (isToricCone_bot i)).analyticRealization h₀) :=
    (ofCone hi (isToricCone_bot i)).contMDiffSMul_complexTorus_analyticRealization h₀ e n
  have hc : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (fun _ : ComplexTorus N ↦
        (ofCone hi (isToricCone_bot i)).analyticDistinguishedPoint h₀ z₀) :=
    contMDiff_const
  exact (hsmul.contMDiff_smul.comp (contMDiff_id.prodMk hc)).congr fun t ↦ by
    simpa only [Function.comp_apply, Prod.fst, Prod.snd, id_eq] using
      (analyticZeroConeHomeomorph_apply hi t).trans
        ((ofCone hi (isToricCone_bot i)).analyticTorusι_def h₀ ⟨z₀⟩ t)

/-- The inverse zero-cone identification is holomorphic: its coordinates are the holomorphic
characters of the zero-cone fan. -/
theorem contMDiff_analyticZeroConeHomeomorph_symm (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, ι → ℂ) n
      (analyticZeroConeHomeomorph hi).symm := by
  intro _
  let _ := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
  have hcomp : ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, ι → ℂ) n
      (complexTorusAmbient e ∘ (analyticZeroConeHomeomorph hi).symm) := by
    rw [contMDiff_pi_space]
    intro j
    let m : IntegralCharacter N := e.symm (Finsupp.single j 1)
    have hm : ∀ σ : (ofCone hi (isToricCone_bot i)).cones,
        m ∈ dualSemigroup (ofCone hi (isToricCone_bot i)).lattice σ.1 := by
      intro σ
      have hσ : σ.1 = (⊥ : PointedCone ℝ V) :=
        le_bot_iff.mp ((mem_ofCone_cones hi (isToricCone_bot i)).mp σ.2).le
      rw [hσ]
      simp
    refine ((ofCone hi (isToricCone_bot i)).contMDiff_analyticCharacter h₀ m hm n).congr
      fun x ↦ ?_
    have hx := (analyticZeroConeHomeomorph hi).apply_symm_apply x
    rw [analyticZeroConeHomeomorph_apply] at hx
    rw [← hx,
      (ofCone hi (isToricCone_bot i)).analyticCharacter_analyticTorusι h₀ m hm ⟨z₀⟩]
    simp [m]
  exact (contMDiff_complexTorusAmbient_comp_iff e).mp hcomp

/-- The canonical biholomorphism from the coordinate-free complex torus to the analytic
realization of the zero-cone fan. It has the existing homeomorphism as its underlying map. -/
noncomputable def analyticZeroConeDiffeomorph (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
    Diffeomorph 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      (ComplexTorus N) ((ofCone hi (isToricCone_bot i)).analyticRealization h₀) n :=
  let _ := complexTorusChartedSpace e
  letI := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
  { toEquiv := (analyticZeroConeHomeomorph hi).toEquiv
    contMDiff_toFun := contMDiff_analyticZeroConeHomeomorph hi e n
    contMDiff_invFun := contMDiff_analyticZeroConeHomeomorph_symm hi e n }

/-- The zero-cone biholomorphism has the canonical torus homeomorphism as its underlying
homeomorphism. -/
@[simp]
theorem analyticZeroConeDiffeomorph_toHomeomorph (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
    (analyticZeroConeDiffeomorph hi e n).toHomeomorph =
      analyticZeroConeHomeomorph hi := by
  let _ := complexTorusChartedSpace e
  let _ := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
  rfl

/-- The zero-cone biholomorphism is the canonical dense-torus inclusion. -/
@[simp]
theorem analyticZeroConeDiffeomorph_apply (n : ℕ∞ω) (t : ComplexTorus N) :
    analyticZeroConeDiffeomorph hi e n t =
      (ofCone hi (isToricCone_bot i)).analyticTorusι h₀ ⟨z₀⟩ t := by
  let _ := complexTorusChartedSpace e
  let _ := (ofCone hi (isToricCone_bot i)).analyticChartedSpace h₀
  calc
    analyticZeroConeDiffeomorph hi e n t =
        (analyticZeroConeDiffeomorph hi e n).toHomeomorph t := rfl
    _ = analyticZeroConeHomeomorph hi t := by
      rw [analyticZeroConeDiffeomorph_toHomeomorph]
    _ = (ofCone hi (isToricCone_bot i)).analyticTorusι h₀ ⟨z₀⟩ t :=
      analyticZeroConeHomeomorph_apply hi t

end TauCeti.Toric.Fan
