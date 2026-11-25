/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.DeterminantLine.Complex
public import TauCeti.Analysis.Fredholm.DeterminantLine.Homotopy

/-!
# Canonical orientations of compact perturbations of complex-linear Fredholm operators

The linearized operator of a pseudoholomorphic sphere, of a component of a nodal curve, or of the
normal directions at a node is a real Cauchy–Riemann operator: a complex-linear operator plus a
term of order zero, which is compact between the relevant Sobolev spaces. Its determinant line
`det (ker T) ⊗ (det (F ⧸ range T))^*` is oriented by deforming the operator to its complex-linear
part, whose determinant line carries the complex orientation
(`LinearMap.IsComplexPositiveDetLine`), and transporting that orientation back along the
deformation (`TauCeti.detLineOrientationTransport`). This file constructs this canonical
orientation and proves that it does not depend on the choices made.

* **Complex orientations.** The complex orientation of a complex-linear Fredholm operator
  (`ContinuousLinearMap.IsFredholm.complexDetLineOrientation`) is carried to the complex
  orientation by orientation transport along any path of complex-linear Fredholm operators
  (`TauCeti.detLineOrientationTransport_complexDetLineOrientation`, in
  `TauCeti.Analysis.Fredholm.DeterminantLine.Complex`).
* **The canonical orientation.** For a complex-linear Fredholm operator `A` and a compact
  real-linear `K`, the operators `A + t K`, `0 ≤ t ≤ 1`, are Fredholm. The canonical orientation
  of the determinant line of `A + K`
  (`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation`) is the complex orientation of
  `A` (`ContinuousLinearMap.IsFredholm.complexDetLineOrientation`) transported along this path. For
  `K = 0` it is the complex orientation of `A`
  (`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_zero`).
* **Families.** Along a path `x ↦ A x + K x` of such operators, with `A` and `K` continuous,
  orientation transport carries the canonical orientation at one end to the canonical orientation
  at the other (`TauCeti.detLineOrientationTransport_canonicalDetLineOrientation`). The proof
  transports around the rectangle `(x, t) ↦ A x + t K x`: its bottom edge is a path of
  complex-linear operators, along which complex orientations are transported to complex
  orientations, and transport around a rectangle commutes
  (`TauCeti.detLineOrientationTransport_comm`).
* **Independence of the splitting.** An operator may be written as a complex-linear Fredholm
  operator plus a compact operator in many ways. All of them give the same canonical orientation
  (`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_congr`): two splittings
  `A + K = A' + K'` are joined by the path of splittings `A + s (A' - A)`, `K + s (K' - K)`, along
  which the operator itself is constant.

## Main definitions

* `ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation`: the canonical orientation of the
  determinant line of a complex-linear Fredholm operator plus a compact operator.

## Main results

* `ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_eq_map`: the canonical orientation
  read along any path pointwise equal to the segment `t ↦ A + t K`.
* `TauCeti.detLineOrientationTransport_canonicalDetLineOrientation`: transport along paths of
  compact perturbations preserves canonical orientations.
* `ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_congr`: the canonical orientation does
  not depend on the splitting into a complex-linear and a compact part.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 3.1 (the orientation of the moduli space of
  simple spheres through the complex-linear part of real Cauchy–Riemann operators) and
  Appendix A.2 (determinant line bundles).
-/

public section

noncomputable section

open Filter Set Topology ContinuousLinearMap Module

namespace ContinuousLinearMap.IsFredholm

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {A : E →L[ℂ] F} {K : E →L[ℝ] F}

/-- The operators `A + t K` on the segment from a complex-linear Fredholm operator `A` to a
compact perturbation `A + K` are Fredholm. -/
theorem restrictScalars_add_smul_of_isCompactOperator (hA : IsFredholm A)
    (hK : IsCompactOperator K) (t : ℝ) : IsFredholm (A.restrictScalars ℝ + t • K) :=
  (hA.restrictScalars ℝ).add_of_isCompactOperator (by simpa using hK.smul t)

/-- The **canonical orientation** of the determinant line of `A + K`, for a complex-linear
Fredholm operator `A` and a compact real-linear operator `K`: the complex orientation of `A`
(`ContinuousLinearMap.IsFredholm.complexDetLineOrientation`) transported along the path of
Fredholm operators `A + t K`, `0 ≤ t ≤ 1` (`TauCeti.detLineOrientationTransport`). It depends only
on the operator `A + K`, not on its splitting
(`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_congr`). -/
def canonicalDetLineOrientation (hA : IsFredholm A) (hK : IsCompactOperator K) :
    Module.Ray ℝ ((A.restrictScalars ℝ + K : E →L[ℝ] F) : E →ₗ[ℝ] F).detLine :=
  Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [one_smul]))
    (detLineOrientationTransport (T := fun t : ℝ ↦ A.restrictScalars ℝ + t • K) 0 1
      (Continuous.continuousOn (by fun_prop))
      (fun t _ ↦ hA.restrictScalars_add_smul_of_isCompactOperator hK t)
      (Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [zero_smul, add_zero]))
        hA.complexDetLineOrientation))

/-- The defining formula of `ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation`: the
complex orientation of `A`, carried to the determinant line of `A + 0 K`, transported along
`t ↦ A + t K` from `0` to `1`, and carried from `A + 1 K` to `A + K`. -/
theorem canonicalDetLineOrientation_def (hA : IsFredholm A) (hK : IsCompactOperator K) :
    hA.canonicalDetLineOrientation hK =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [one_smul]))
        (detLineOrientationTransport (T := fun t : ℝ ↦ A.restrictScalars ℝ + t • K) 0 1
          (Continuous.continuousOn (by fun_prop))
          (fun t _ ↦ hA.restrictScalars_add_smul_of_isCompactOperator hK t)
          (Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [zero_smul, add_zero]))
            hA.complexDetLineOrientation)) := by
  rw [canonicalDetLineOrientation]

/-- The canonical orientation of `A + K` is the complex orientation of `A` transported along any
path `P` which is pointwise equal to the segment `t ↦ A + t K`. -/
theorem canonicalDetLineOrientation_eq_map (hA : IsFredholm A) (hK : IsCompactOperator K)
    {P : ℝ → E →L[ℝ] F} (hP : ∀ t, P t = A.restrictScalars ℝ + t • K)
    (hPc : ContinuousOn P (uIcc 0 1)) (hPF : ∀ t ∈ uIcc (0 : ℝ) 1, IsFredholm (P t)) :
    hA.canonicalDetLineOrientation hK =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by rw [hP, one_smul]))
        (detLineOrientationTransport 0 1 hPc hPF
          (Module.Ray.map (LinearMap.detLineCongrOfEq (by rw [hP, zero_smul, add_zero]))
            hA.complexDetLineOrientation)) := by
  obtain rfl : P = fun t ↦ A.restrictScalars ℝ + t • K := funext hP
  exact hA.canonicalDetLineOrientation_def hK

end ContinuousLinearMap.IsFredholm

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Transport preserves canonical orientations.** Let `A` be a path of complex-linear Fredholm
operators and `K` a path of compact real-linear operators, both continuous between `a` and `b`.
Orientation transport along the path `A + K` carries the canonical orientation of `A a + K a` to
the canonical orientation of `A b + K b`. -/
theorem detLineOrientationTransport_canonicalDetLineOrientation {A : ℝ → E →L[ℂ] F}
    {K : ℝ → E →L[ℝ] F} {a b : ℝ} (hA : ContinuousOn A (uIcc a b))
    (hK : ContinuousOn K (uIcc a b)) (hAF : ∀ x ∈ uIcc a b, IsFredholm (A x))
    (hKc : ∀ x ∈ uIcc a b, IsCompactOperator (K x)) :
    detLineOrientationTransport (T := fun x ↦ (A x).restrictScalars ℝ + K x) a b
        (((restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hA).add hK)
        (fun x hx ↦ ((hAF x hx).restrictScalars ℝ).add_of_isCompactOperator (hKc x hx))
        ((hAF a left_mem_uIcc).canonicalDetLineOrientation (hKc a left_mem_uIcc)) =
      (hAF b right_mem_uIcc).canonicalDetLineOrientation (hKc b right_mem_uIcc) := by
  -- Transport around the rectangle `H (x, t) = A x + t K x`, `x ∈ [[a, b]]`, `t ∈ [0, 1]`. Its
  -- vertical edges define the canonical orientations, its bottom edge is complex-linear, and its
  -- top edge is the path `A + K`. `H` is kept opaque, and its edges are compared with these paths
  -- through pointwise equalities.
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × ℝ → E →L[ℝ] F,
      H = fun p ↦ (A p.1).restrictScalars ℝ + p.2 • K p.1 := ⟨_, rfl⟩
  have hHapp (x t : ℝ) : H (x, t) = (A x).restrictScalars ℝ + t • K x := by rw [hHdef]
  have hAℝ := (restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hA
  have hfst : MapsTo Prod.fst (uIcc a b ×ˢ uIcc (0 : ℝ) 1) (uIcc a b) := fun _ hp ↦ hp.1
  have hH : ContinuousOn H (uIcc a b ×ˢ uIcc 0 1) := by
    rw [hHdef]
    exact (hAℝ.comp continuousOn_fst hfst).add
      (continuousOn_snd.smul (hK.comp continuousOn_fst hfst))
  have hHF (p : ℝ × ℝ) (hp : p ∈ uIcc a b ×ˢ uIcc 0 1) : IsFredholm (H p) := by
    rw [hHdef]
    exact (hAF p.1 hp.1).restrictScalars_add_smul_of_isCompactOperator (hKc p.1 hp.1) p.2
  have hvert (x : ℝ) (hx : x ∈ uIcc a b) :=
    (hAF x hx).canonicalDetLineOrientation_eq_map (hKc x hx) (P := fun t ↦ H (x, t)) (hHapp x)
      (hH.comp (Continuous.prodMk_right x).continuousOn fun _ ht ↦ ⟨hx, ht⟩)
      (fun t ht ↦ hHF _ ⟨hx, ht⟩)
  have hhor (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : ContinuousOn (fun x ↦ H (x, t)) (uIcc a b) :=
    hH.comp (Continuous.prodMk_left t).continuousOn fun _ hx ↦ ⟨hx, ht⟩
  have hbot := detLineOrientationTransport_map_detLineCongrOfEq
    (T₁ := fun x ↦ (A x).restrictScalars ℝ) (T₂ := fun x ↦ H (x, 0))
    (fun x ↦ by rw [hHapp, zero_smul, add_zero]) hAℝ (fun x hx ↦ (hAF x hx).restrictScalars ℝ)
    (hhor 0 left_mem_uIcc) (fun x hx ↦ hHF _ ⟨hx, left_mem_uIcc⟩)
    (hAF a left_mem_uIcc).complexDetLineOrientation
  rw [detLineOrientationTransport_complexDetLineOrientation hA hAF] at hbot
  have htop := detLineOrientationTransport_map_detLineCongrOfEq
    (T₁ := fun x ↦ H (x, 1)) (T₂ := fun x ↦ (A x).restrictScalars ℝ + K x)
    (fun x ↦ by rw [hHapp, one_smul]) (hhor 1 right_mem_uIcc)
    (fun x hx ↦ hHF _ ⟨hx, right_mem_uIcc⟩) (hAℝ.add hK)
    (fun x hx ↦ ((hAF x hx).restrictScalars ℝ).add_of_isCompactOperator (hKc x hx))
  -- Up the left edge, along the top edge, then around the rectangle and down the right edge.
  calc _ = _ := congrArg _ (hvert a left_mem_uIcc)
    -- Along the top edge `H (·, 1)` rather than the path `A + K`.
    _ = _ := htop _
    -- Around the rectangle: along the bottom edge, then up the right edge.
    _ = _ := congrArg _ (detLineOrientationTransport_comm hH hHF _)
    -- The bottom edge is complex-linear.
    _ = _ := congrArg _ (congrArg _ hbot)
    _ = _ := (hvert b right_mem_uIcc).symm

/-- Equal splittings give the same canonical orientation, once the determinant lines of the equal
operators are identified. -/
private theorem map_detLineCongrOfEq_canonicalDetLineOrientation {A₁ A₂ : E →L[ℂ] F}
    {K₁ K₂ : E →L[ℝ] F} (hA₁ : IsFredholm A₁) (hK₁ : IsCompactOperator K₁) (hA₂ : IsFredholm A₂)
    (hK₂ : IsCompactOperator K₂) (hA : A₁ = A₂) (hK : K₁ = K₂) :
    Module.Ray.map (LinearMap.detLineCongrOfEq (by rw [hA, hK]))
        (hA₁.canonicalDetLineOrientation hK₁) =
      hA₂.canonicalDetLineOrientation hK₂ := by
  subst hA hK
  simp only [LinearMap.detLineCongrOfEq_rfl, Module.Ray.map_refl, Equiv.refl_apply]

end TauCeti

namespace ContinuousLinearMap.IsFredholm

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {A : E →L[ℂ] F}

/-- The canonical orientation of a complex-linear Fredholm operator, with no compact part, is its
complex orientation. -/
theorem canonicalDetLineOrientation_zero (hA : IsFredholm A) :
    hA.canonicalDetLineOrientation (K := 0) isCompactOperator_zero =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by rw [add_zero]))
        hA.complexDetLineOrientation := by
  -- Along the constant path at `A`, transport is the identity.
  calc _ = _ := hA.canonicalDetLineOrientation_eq_map (K := 0) isCompactOperator_zero
        (P := fun _ ↦ A.restrictScalars ℝ) (fun t ↦ by rw [smul_zero, add_zero])
        continuousOn_const (fun _ _ ↦ hA.restrictScalars ℝ)
    _ = _ := congrArg _ (congrFun (detLineOrientationTransport_const (hA.restrictScalars ℝ) 0 1) _)
    _ = _ := LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq _ _ _

omit [CompleteSpace E] [CompleteSpace F] in
/-- Two splittings `A + K = A' + K'` into complex-linear and real-linear parts differ by
`A' - A = K - K'`. -/
private theorem sub_eq_sub_of_restrictScalars_add_eq {A' : E →L[ℂ] F} {K K' : E →L[ℝ] F}
    (h : A.restrictScalars ℝ + K = A'.restrictScalars ℝ + K') (v : E) :
    A' v - A v = K v - K' v := by
  have hv := congrArg (fun T : E →L[ℝ] F ↦ T v) h
  simp only [add_apply, coe_restrictScalars'] at hv
  linear_combination (norm := module) (-1 : ℝ) • hv

/-- **The canonical orientation does not depend on the splitting.** If `A + K = A' + K'` for
complex-linear Fredholm operators `A`, `A'` and compact real-linear operators `K`, `K'`, the
canonical orientations of the two splittings agree, once the determinant lines of the equal
operators are identified. -/
theorem canonicalDetLineOrientation_congr {A' : E →L[ℂ] F} {K K' : E →L[ℝ] F} (hA : IsFredholm A)
    (hK : IsCompactOperator K) (hA' : IsFredholm A') (hK' : IsCompactOperator K')
    (h : A.restrictScalars ℝ + K = A'.restrictScalars ℝ + K') :
    Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg _ h))
        (hA.canonicalDetLineOrientation hK) =
      hA'.canonicalDetLineOrientation hK' := by
  -- The splittings `A + s (A' - A)` and `K + s (K' - K)` join the two, and their sum is constant.
  -- The paths are kept opaque, and compared with their values through pointwise equalities.
  obtain ⟨B, hB⟩ : ∃ B : ℝ → E →L[ℂ] F, B = fun s ↦ A + s • (A' - A) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ → E →L[ℝ] F, L = fun s ↦ K + s • (K' - K) := ⟨_, rfl⟩
  have hsplit := sub_eq_sub_of_restrictScalars_add_eq h
  have hdiff : IsCompactOperator (A' - A) := by
    rw [show ⇑(A' - A) = ⇑(K - K') from funext fun v ↦ by simp only [sub_apply, hsplit]]
    simpa using hK.sub hK'
  have hBF (s : ℝ) : IsFredholm (B s) := by
    rw [hB]
    exact hA.add_of_isCompactOperator (by simpa using hdiff.smul s)
  have hLc (s : ℝ) : IsCompactOperator (L s) := by
    rw [hL]
    simpa using hK.add ((hK'.sub hK).smul s)
  have hT (s : ℝ) : (B s).restrictScalars ℝ + L s = A.restrictScalars ℝ + K := by
    rw [hB, hL]
    ext v
    simp only [add_apply, coe_restrictScalars', smul_apply, sub_apply, hsplit]
    module
  have hBc : Continuous B := by rw [hB]; fun_prop
  have hLc' : Continuous L := by rw [hL]; fun_prop
  have hB₀ : A = B 0 := by simp [hB]
  have hL₀ : K = L 0 := by simp [hL]
  have hB₁ : B 1 = A' := by simp [hB]
  have hL₁ : L 1 = K' := by simp [hL]
  -- The path `B + L` is pointwise equal to the constant path at `A + K`, along which transport is
  -- the identity.
  have hconst := detLineOrientationTransport_map_detLineCongrOfEq
    (T₁ := fun _ ↦ A.restrictScalars ℝ + K) (T₂ := fun s ↦ (B s).restrictScalars ℝ + L s)
    (a := 0) (b := 1) (fun s ↦ (hT s).symm) continuousOn_const
    (fun _ _ ↦ (hA.restrictScalars ℝ).add_of_isCompactOperator hK)
    (((restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hBc.continuousOn).add
      hLc'.continuousOn)
    (fun s _ ↦ ((hBF s).restrictScalars ℝ).add_of_isCompactOperator (hLc s))
    (hA.canonicalDetLineOrientation hK)
  simp only [detLineOrientationTransport_const, id_eq] at hconst
  symm
  calc _ = _ :=
        (map_detLineCongrOfEq_canonicalDetLineOrientation (hBF 1) (hLc 1) hA' hK' hB₁ hL₁).symm
    -- Along the path of splittings, transport carries canonical orientations to canonical ones.
    _ = _ := congrArg _ (detLineOrientationTransport_canonicalDetLineOrientation (a := 0) (b := 1)
        hBc.continuousOn hLc'.continuousOn (fun s _ ↦ hBF s) (fun s _ ↦ hLc s)).symm
    _ = _ := congrArg _ (congrArg _
        (map_detLineCongrOfEq_canonicalDetLineOrientation hA hK (hBF 0) (hLc 0) hB₀ hL₀).symm)
    -- The operators of that path are all equal to `A + K`.
    _ = _ := congrArg _ hconst
    _ = _ := LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq _ _ _

end ContinuousLinearMap.IsFredholm
