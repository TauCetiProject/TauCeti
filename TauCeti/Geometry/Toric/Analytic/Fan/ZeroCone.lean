/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Affine.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Character
public import TauCeti.Geometry.Toric.Analytic.Fan.TorusAction.Holomorphic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# The analytic zero-cone fan and the dense torus are the complex torus

The canonical identification of the realization of the zero-cone fan with the coordinate-free
complex torus is a biholomorphism. Its forward map is the dense-torus inclusion. The inverse is
holomorphic because each torus coordinate is the global character function of the corresponding
integral character; every character is nonnegative on the zero cone.

The statement uses any finite free presentation of the character lattice. Thus the complex
structure on the torus and the analytic structure obtained by gluing the zero-cone fan agree
without a preferred integral basis.

For every nonempty regular fan, the dense torus is an open complex submanifold of the
realization, biholomorphic to the complex torus by the canonical torus inclusion. The inclusion
factors through the zero-cone fan: the torus is biholomorphic to the realization of the zero-cone
fan, hence to the affine chart of the zero cone, and the inclusion of that chart in the
realization is a biholomorphism onto its open image.

## Main declarations

* `TauCeti.Toric.Fan.analyticZeroConeDiffeomorph`: the realization of the zero-cone fan is
  biholomorphic to the complex torus.
* `TauCeti.Toric.Fan.isLocalDiffeomorph_analyticTorusι`: the canonical torus inclusion is a local
  biholomorphism.
* `TauCeti.Toric.Fan.analyticTorusPartialDiffeomorph`: the canonical torus inclusion as a
  biholomorphism from the complex torus onto the analytic dense torus.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.1 and 1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} {ι : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] [Fintype ι] {i : N →+ V}

section ZeroCone

variable (hi : IsIntegralLattice i) (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

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
  exact ((Φ₀).contMDiff_analyticTorusι h₀ ⟨z₀⟩ e n).congr (analyticZeroConeHomeomorph_apply hi)

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
    rw [contMDiff_pi_module_iff]
    intro j
    let m : IntegralCharacter N := e.symm (Finsupp.single j 1)
    have hm := mem_dualSemigroup_ofCone_bot hi m
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

end ZeroCone

section DenseTorus

variable (Φ : Fan i) (hΦ : Φ.IsRegular) (hΦ0 : Nonempty Φ.cones)
  (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

/-- The canonical torus inclusion into the realization of a nonempty regular fan is a local
biholomorphism, for any finite free presentation of the character lattice. -/
theorem isLocalDiffeomorph_analyticTorusι (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := Φ.analyticChartedSpace hΦ
    IsLocalDiffeomorph 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Φ.analyticTorusι hΦ hΦ0) := by
  intro _
  let _ := Φ.analyticChartedSpace hΦ
  let τ : Φ.cones := ⟨⊥, Φ.bot_mem hΦ0.some.2⟩
  have hbot := isRegularCone_bot Φ.lattice
  obtain ⟨l, B, hB⟩ := hbot.exists_basis_sum
  have : Finite (ToricRay (⊥ : PointedCone ℝ V)) := ToricRay.finite_of_fg hbot.fg
  let κ := Finite.equivFin (ToricRay (⊥ : PointedCone ℝ V))
  let g := (Φ.analyticChartGenerators τ).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice hbot.toIsToricCone hB κ g
  let _ := (ofCone Φ.lattice (isToricCone_bot i)).analyticChartedSpace
    (isRegular_ofCone Φ.lattice hbot)
  -- The inclusion is the biholomorphism `D` of the torus with the affine chart of the zero cone,
  -- through the realization of the zero-cone fan, followed by the inclusion `P` of that chart,
  -- a biholomorphism onto its open image.
  let D := (analyticZeroConeDiffeomorph Φ.lattice e n).trans
    (analyticOfConeDiffeomorph Φ.lattice hbot hB κ g n).symm
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ τ hB κ g n
  let z : (ofCone Φ.lattice (isToricCone_bot i)).cones :=
    ⟨⊥, (mem_ofCone_cones Φ.lattice (isToricCone_bot i)).2 (PointedCone.IsFaceOf.refl ⊥)⟩
  have hD : ∀ t, D t = t • (default : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice ⊥)) :=
    fun t ↦ by
      rw [Diffeomorph.coe_trans, Function.comp_apply, analyticZeroConeDiffeomorph_apply,
        analyticTorusι_eq_analyticAffineChartι _ _ _ z t]
      exact analyticOfConeDiffeomorph_symm_analyticAffineChartι_top Φ.lattice hbot hB κ g n _
  have hι : Φ.analyticTorusι hΦ hΦ0 = P ∘ D := funext fun t ↦ by
    rw [Function.comp_apply, hD, analyticAffineChartPartialDiffeomorph_apply,
      Φ.analyticTorusι_eq_analyticAffineChartι hΦ hΦ0 τ t]
  rw [hι]
  have hPs : ∀ t, D t ∈ P.source := fun t ↦ by
    simp only [P, analyticAffineChartPartialDiffeomorph_source, Set.mem_univ]
  exact fun t ↦ (D.isLocalDiffeomorph t).comp (hg := P.isLocalDiffeomorphAt _ _ _ (hPs t))

/-- The canonical torus inclusion into the realization of a nonempty regular fan is a
biholomorphism from the complex torus onto the analytic dense torus, an open subset of the
realization. -/
noncomputable def analyticTorusPartialDiffeomorph (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := Φ.analyticChartedSpace hΦ
    PartialDiffeomorph 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      (ComplexTorus N) (Φ.analyticRealization hΦ) n :=
  let _ := complexTorusChartedSpace e
  letI := Φ.analyticChartedSpace hΦ
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn
    ((Φ.isLocalDiffeomorph_analyticTorusι hΦ hΦ0 e n).isLocalDiffeomorphOn Set.univ) isOpen_univ
    (Φ.analyticTorusι_injective hΦ hΦ0).injOn

/-- The biholomorphism onto the dense torus is the canonical torus inclusion. -/
@[simp]
theorem coe_analyticTorusPartialDiffeomorph (n : ℕ∞ω) :
    ⇑(Φ.analyticTorusPartialDiffeomorph hΦ hΦ0 e n) = Φ.analyticTorusι hΦ hΦ0 := by
  simp [analyticTorusPartialDiffeomorph]

/-- The biholomorphism onto the dense torus is defined on the whole torus. -/
@[simp]
theorem analyticTorusPartialDiffeomorph_source (n : ℕ∞ω) :
    (Φ.analyticTorusPartialDiffeomorph hΦ hΦ0 e n).source = Set.univ := by
  simp [analyticTorusPartialDiffeomorph]

/-- The image of the biholomorphism onto the dense torus is the analytic dense torus. -/
@[simp]
theorem analyticTorusPartialDiffeomorph_target (n : ℕ∞ω) :
    (Φ.analyticTorusPartialDiffeomorph hΦ hΦ0 e n).target = Φ.analyticDenseTorus hΦ hΦ0 := by
  simp [analyticTorusPartialDiffeomorph]

/-- The inverse of the biholomorphism onto the dense torus recovers a torus point from its
canonical inclusion. -/
@[simp]
theorem analyticTorusPartialDiffeomorph_symm_analyticTorusι (n : ℕ∞ω) (t : ComplexTorus N) :
    let _ := complexTorusChartedSpace e
    letI := Φ.analyticChartedSpace hΦ
    (Φ.analyticTorusPartialDiffeomorph hΦ hΦ0 e n).toPartialEquiv.symm
      (Φ.analyticTorusι hΦ hΦ0 t) = t := by
  intro _
  let _ := Φ.analyticChartedSpace hΦ
  rw [← coe_analyticTorusPartialDiffeomorph Φ hΦ hΦ0 e n]
  exact (Φ.analyticTorusPartialDiffeomorph hΦ hΦ0 e n).toPartialEquiv.left_inv
    ((analyticTorusPartialDiffeomorph_source Φ hΦ hΦ0 e n).symm ▸ Set.mem_univ t)

end DenseTorus

end TauCeti.Toric.Fan
