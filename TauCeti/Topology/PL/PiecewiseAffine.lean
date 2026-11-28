/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.FiniteInf
public import TauCeti.Topology.PL.Product
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Baire.Lemmas
import TauCeti.Topology.Algebra.ContinuousAffineMap
import TauCeti.Topology.Connected.FiniteFamily

/-!
# Algebraic, lattice, and selection properties of piecewise-affine maps

Global piecewise affineness (`TauCeti.IsPiecewiseAffineOn`) is closed under vector-space
operations, pointwise maxima and minima, finite maxima and minima of continuous affine
functionals, and the coordinatewise rectifier on finite coordinate spaces.

On `ℝ`-valued functions over a real topological vector space, global piecewise affineness is
characterized as continuity together with pointwise membership in a finite family of continuous
affine functionals (`TauCeti.isPiecewiseAffineOn_univ_iff_continuous_exists_eq`). The sufficiency
argument considers the open dense complement of the pairwise equalizer hyperplanes `A i = A j`
for distinct functionals in the family: on each nonempty strict sign cell, the functionals take
pairwise distinct values, so continuity forces `f` to agree with a single functional there and
hence on its polyhedral closure.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {f g : E → F} {V : Set E}

/-- Negating a piecewise-affine map preserves piecewise affineness. -/
theorem IsPiecewiseAffineOn.neg [ContinuousNeg F] (hf : IsPiecewiseAffineOn f V) :
    IsPiecewiseAffineOn (-f) V :=
  (isPiecewiseAffineOn_continuousAffineMap
    ({ toLinearMap := -LinearMap.id, cont := continuous_neg } : F →L[ℝ] F).toContinuousAffineMap
      univ).comp
    hf (mapsTo_univ _ _)

/-- Scaling a piecewise-affine map by a constant preserves piecewise affineness. -/
theorem IsPiecewiseAffineOn.const_smul [ContinuousConstSMul ℝ F] (c : ℝ)
    (hf : IsPiecewiseAffineOn f V) : IsPiecewiseAffineOn (c • f) V := by
  obtain ⟨n, C, A, hC, hcov, heq⟩ := isPiecewiseAffineOn_iff.mp hf
  exact isPiecewiseAffineOn_iff.mpr
    ⟨n, C, fun i => c • A i, hC, hcov, fun i x hx => congrArg (c • ·) (heq i hx)⟩

/-- Adding two piecewise-affine maps on the same set preserves piecewise affineness. -/
theorem IsPiecewiseAffineOn.add [ContinuousAdd F] (hf : IsPiecewiseAffineOn f V)
    (hg : IsPiecewiseAffineOn g V) : IsPiecewiseAffineOn (f + g) V :=
  (isPiecewiseAffineOn_continuousAffineMap
    (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F).toContinuousAffineMap
      univ).comp (hf.prodMk hg) (mapsTo_univ _ _)

/-- Subtracting two piecewise-affine maps on the same set preserves piecewise affineness. -/
theorem IsPiecewiseAffineOn.sub [ContinuousAdd F] [ContinuousNeg F] (hf : IsPiecewiseAffineOn f V)
    (hg : IsPiecewiseAffineOn g V) : IsPiecewiseAffineOn (f - g) V := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- A finite sum of piecewise-affine maps on the same set is piecewise affine. -/
theorem IsPiecewiseAffineOn.sum [ContinuousAdd F] {ι : Type*} (s : Finset ι)
    {φ : ι → E → F} (hφ : ∀ i ∈ s, IsPiecewiseAffineOn (φ i) V) :
    IsPiecewiseAffineOn (∑ i ∈ s, φ i) V := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h0 : IsPiecewiseAffineOn (0 : E → F) V :=
      (isPiecewiseAffineOn_continuousAffineMap (0 : E →ᴬ[ℝ] F) V).congr fun _ _ => by simp
    simpa only [Finset.sum_empty] using h0
  | @insert a s has ih =>
    rw [Finset.sum_insert has]
    exact (hφ a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hφ i (Finset.mem_insert_of_mem hi))

/-- Pointwise maximum of two coordinates on `ℝ × ℝ` is piecewise affine on the whole plane. -/
theorem isPiecewiseAffineOn_max_prod :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => max p.1 p.2) (Set.univ : Set (ℝ × ℝ)) := by
  let f : Bool → (ℝ × ℝ) →ᴬ[ℝ] ℝ := fun b =>
    cond b (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  refine isPiecewiseAffineOn_of_finite (ι := Bool)
    (C := fun b => {p : ℝ × ℝ | (f (!b) - f b) p ≤ 0}) (A := f)
    (fun b => isConvexPolyhedron_setOf_le _) ?_ ?_
  · intro p _
    rcases le_total p.1 p.2 with h | h
    · exact mem_iUnion.mpr ⟨false, by simpa [f] using h⟩
    · exact mem_iUnion.mpr ⟨true, by simpa [f] using h⟩
  · rintro (_ | _) p ⟨-, hp⟩
    · simpa [f, max_eq_right] using hp
    · simpa [f, max_eq_left] using hp

/-- Pointwise maximum of two real-valued piecewise-affine maps is piecewise affine. -/
theorem IsPiecewiseAffineOn.sup {f g : E → ℝ} (hf : IsPiecewiseAffineOn f V)
    (hg : IsPiecewiseAffineOn g V) : IsPiecewiseAffineOn (f ⊔ g) V :=
  isPiecewiseAffineOn_max_prod.comp (hf.prodMk hg) (mapsTo_univ _ _)

/-- Pointwise minimum of two real-valued piecewise-affine maps is piecewise affine. -/
theorem IsPiecewiseAffineOn.inf {f g : E → ℝ} (hf : IsPiecewiseAffineOn f V)
    (hg : IsPiecewiseAffineOn g V) : IsPiecewiseAffineOn (f ⊓ g) V := by
  have hinf : f ⊓ g = -((-f) ⊔ (-g)) := by
    ext x
    simp [max_neg_neg]
  rw [hinf]
  exact (hf.neg.sup hg.neg).neg

/-- Pointwise absolute value of a real-valued piecewise-affine map is piecewise affine. -/
theorem IsPiecewiseAffineOn.abs {f : E → ℝ} (hf : IsPiecewiseAffineOn f V) :
    IsPiecewiseAffineOn (fun x => |f x|) V := by
  have habs : (fun x => |f x|) = f ⊔ (-f) := by
    funext x
    exact abs_eq_max_neg
  rw [habs]
  exact hf.sup hf.neg

/-- A finite pointwise maximum of real-valued piecewise-affine maps is piecewise affine. -/
theorem IsPiecewiseAffineOn.finset_sup'_apply {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {φ : ι → E → ℝ} (hφ : ∀ i ∈ s, IsPiecewiseAffineOn (φ i) V) :
    IsPiecewiseAffineOn (fun x => s.sup' hs (fun i => φ i x)) V := by
  simpa only [← Finset.sup'_apply] using
    Finset.sup'_induction (p := fun g => IsPiecewiseAffineOn g V) hs φ
      (fun _ ha _ hb => ha.sup hb) hφ

/-- A finite pointwise minimum of real-valued piecewise-affine maps is piecewise affine. -/
theorem IsPiecewiseAffineOn.finset_inf'_apply {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {φ : ι → E → ℝ} (hφ : ∀ i ∈ s, IsPiecewiseAffineOn (φ i) V) :
    IsPiecewiseAffineOn (fun x => s.inf' hs (fun i => φ i x)) V := by
  simpa only [← Finset.inf'_apply] using
    Finset.inf'_induction (p := fun g => IsPiecewiseAffineOn g V) hs φ
      (fun _ ha _ hb => ha.inf hb) hφ

end TauCeti

namespace Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A finite maximum of continuous affine functionals is piecewise affine on the whole space. -/
theorem isPiecewiseAffineOn_supAffine {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) :
    TauCeti.IsPiecewiseAffineOn (fun x => s.sup' hs (fun i => f i x)) (Set.univ : Set E) :=
  TauCeti.IsPiecewiseAffineOn.finset_sup'_apply s hs fun i _ =>
    TauCeti.isPiecewiseAffineOn_continuousAffineMap (f i) Set.univ

/-- A finite maximum of continuous affine functionals is piecewise linear on the whole source. -/
theorem isPLOn_supAffine {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) :
    TauCeti.IsPLOn (fun x => s.sup' hs (fun i => f i x)) (Set.univ : Set E) :=
  (s.isPiecewiseAffineOn_supAffine hs f).isPLOn

end Finset

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The coordinatewise rectifier `x ↦ (max 0 (x i))ᵢ` on a finite real coordinate space is
piecewise affine on the whole space, with one orthant cell per sign pattern. -/
theorem isPiecewiseAffineOn_pi_max_zero (ι : Type*) [Finite ι] :
    IsPiecewiseAffineOn (fun (x : ι → ℝ) i => max 0 (x i)) (Set.univ : Set (ι → ℝ)) := by
  let C : (ι → Bool) → Set (ι → ℝ) := fun s =>
    {x | ∀ i, (if s i then -(ContinuousLinearMap.proj (R := ℝ) i)
      else ContinuousLinearMap.proj (R := ℝ) i).toContinuousAffineMap x ≤ 0}
  let A : (ι → Bool) → (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) := fun s =>
    (ContinuousLinearMap.pi fun i =>
      if s i then ContinuousLinearMap.proj (R := ℝ) i else 0).toContinuousAffineMap
  refine isPiecewiseAffineOn_of_finite (C := C) (A := A)
    (fun s => isConvexPolyhedron_setOf_forall _) ?_ ?_
  · intro x _
    refine mem_iUnion.mpr ⟨fun i => decide (0 ≤ x i), fun i => ?_⟩
    by_cases hi : 0 ≤ x i
    · simp [hi]
    · simp [hi, (not_le.mp hi).le]
  · intro s x hx
    ext i
    have hxi := hx.2 i
    by_cases hsi : s i
    · simp only [hsi, ↓reduceIte, ContinuousLinearMap.coe_toContinuousAffineMap,
        neg_apply, ContinuousLinearMap.proj_apply, neg_nonpos] at hxi
      simp [A, hsi, max_eq_right hxi]
    · simp only [hsi, Bool.false_eq_true, ↓reduceIte,
        ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.proj_apply] at hxi
      simp [A, hsi, max_eq_left hxi]

/-! ### Selection characterization -/

/-- A function `E → ℝ` on a real topological vector space is globally piecewise affine if and
only if it is continuous and agrees pointwise with some finite family of continuous affine
functionals. -/
theorem isPiecewiseAffineOn_univ_iff_continuous_exists_eq
    [ContinuousAdd E] [ContinuousSMul ℝ E] {f : E → ℝ} :
    IsPiecewiseAffineOn f (Set.univ : Set E) ↔
      Continuous f ∧
        ∃ (n : ℕ) (A : Fin n → (E →ᴬ[ℝ] ℝ)), ∀ x, ∃ i, f x = A i x := by
  constructor
  · intro hf
    refine ⟨continuousOn_univ.mp hf.continuousOn, ?_⟩
    obtain ⟨n, C, A, -, hcov, heq⟩ := isPiecewiseAffineOn_iff.mp hf
    refine ⟨n, A, fun x => ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov (mem_univ x))
    exact ⟨i, heq i ⟨mem_univ x, hi⟩⟩
  · rintro ⟨hf, n, A, hA⟩
    classical
    let S : Finset (E →ᴬ[ℝ] ℝ) := Finset.univ.image A
    let D := S.offDiag
    let g : D → (E →ᴬ[ℝ] ℝ) := fun p => p.val.1 - p.val.2
    let ι :=
      {σ : D → SignType // (∀ p, σ p ≠ 0) ∧ (TauCeti.Convex.signCell g σ).Nonempty}
    have hmemS : ∀ x : E, ∃ a ∈ S, f x = a x := fun x => by
      obtain ⟨i, hi⟩ := hA x
      exact ⟨A i, Finset.mem_image_of_mem A (Finset.mem_univ i), hi⟩
    have hpiece : ∀ σ : ι, ∃ a ∈ S, EqOn f a (TauCeti.Convex.signCell g σ.val) := by
      intro σ
      let U := TauCeti.Convex.signCell g σ.val
      obtain ⟨x₀, hx₀⟩ := σ.property.2
      obtain ⟨a₀, ha₀, hfx₀⟩ := hmemS x₀
      have : PreconnectedSpace U :=
        isPreconnected_iff_preconnectedSpace.mp
          ((TauCeti.Convex.convex_signCell g σ.val).isConnected σ.property.2).isPreconnected
      have heq : (fun x : U => a₀ x.val) = (fun x : U => f x.val) :=
        eq_of_continuous_mem_range (B := U) (Y := ℝ) (ι := S)
          (r := fun a x => a.val x.val) (f := fun x => f x.val)
          (i := ⟨a₀, ha₀⟩) (b₀ := ⟨x₀, hx₀⟩)
          (fun a => a.val.continuous.comp continuous_subtypeVal)
          (hf.comp continuous_subtypeVal)
          (fun x j hj => by
            by_contra hne
            have hval : j.val ≠ a₀ := fun h => hne (Subtype.ext h)
            have hsign := (TauCeti.Convex.mem_signCell.mp x.property)
              ⟨(j.val, a₀), Finset.mem_offDiag.mpr ⟨j.property, ha₀, hval⟩⟩
            have hne0 : g ⟨(j.val, a₀), Finset.mem_offDiag.mpr ⟨j.property, ha₀, hval⟩⟩
                x.val ≠ 0 := by
              rw [← sign_ne_zero, hsign]
              exact σ.property.1 _
            exact hne0 (sub_eq_zero.mpr hj))
          (fun x => by
            obtain ⟨a, ha, hfa⟩ := hmemS x.val
            exact ⟨⟨a, ha⟩, hfa.symm⟩)
          hfx₀.symm
      exact ⟨a₀, ha₀, fun x hx => (congrFun heq ⟨x, hx⟩).symm⟩
    choose piece _ hpiece_eq using hpiece
    refine isPiecewiseAffineOn_of_finite (ι := ι)
      (C := fun σ => closure (TauCeti.Convex.signCell g σ.val)) (A := piece)
      (fun σ => TauCeti.Convex.isConvexPolyhedron_closure_signCell) ?_
      (fun σ x hx => (hpiece_eq σ).closure hf (piece σ).continuous hx.2)
    have hdense_inter : Dense (⋂ p : D, {x : E | g p x ≠ 0}) := by
      rw [← Set.sInter_range]
      refine (Set.finite_range _).dense_sInter ?_ ?_
      · rintro _ ⟨p, rfl⟩
        exact isOpen_ne_fun (g p).continuous continuous_const
      · rintro _ ⟨p, rfl⟩
        exact ContinuousAffineMap.dense_setOf_ne_zero
          (sub_ne_zero.mpr (Finset.mem_offDiag.mp p.property).2.2)
    have hinter_sub :
        (⋂ p : D, {x : E | g p x ≠ 0}) ⊆ ⋃ σ : ι, TauCeti.Convex.signCell g σ.val := by
      intro x hx
      simp only [mem_iInter, mem_ofPred_eq] at hx
      let σ₀ : D → SignType := fun p => SignType.sign (g p x)
      have hσ₀ : ∀ p, σ₀ p ≠ 0 := fun p => sign_ne_zero.mpr (hx p)
      have hx₀ : x ∈ TauCeti.Convex.signCell g σ₀ := TauCeti.Convex.mem_signCell_sign g x
      exact mem_iUnion.mpr ⟨⟨σ₀, hσ₀, ⟨x, hx₀⟩⟩, hx₀⟩
    have huniv : (⋃ σ : ι, closure (TauCeti.Convex.signCell g σ.val)) = Set.univ := by
      rw [← closure_iUnion_of_finite]
      exact eq_univ_of_subset (closure_mono hinter_sub) hdense_inter.closure_eq
    rw [huniv]

end TauCeti
