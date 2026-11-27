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

namespace Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A finite minimum of continuous affine functionals is piecewise affine on the whole space. -/
theorem isPiecewiseAffineOn_infAffine {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) :
    TauCeti.IsPiecewiseAffineOn (fun x => s.inf' hs (fun i => f i x)) (Set.univ : Set E) := by
  refine TauCeti.isPiecewiseAffineOn_of_finite
    (C := s.infCell f) (A := fun i => f i)
    (fun i => s.isConvexPolyhedron_infCell f i) (s.subset_iUnion_infCell hs f) ?_
  intro i x hx
  exact s.infAffine_eq_of_mem_infCell hs f i hx.2

end Finset

namespace TauCeti

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {f g : E → F} {V : Set E}

/-- Negating a piecewise-affine map preserves piecewise affineness. -/
theorem IsPiecewiseAffineOn.neg [ContinuousNeg F] (hf : IsPiecewiseAffineOn f V) :
    IsPiecewiseAffineOn (-f) V :=
  (isPiecewiseAffineOn_continuousAffineMap
    ({ toFun := fun y : F => -y
       map_add' := neg_add
       map_smul' := fun r y => (smul_neg r y).symm
       cont := continuous_neg } : F →L[ℝ] F).toContinuousAffineMap univ).comp
    hf (mapsTo_univ _ _)

/-- Scaling a piecewise-affine map by a constant preserves piecewise affineness. -/
theorem IsPiecewiseAffineOn.const_smul [ContinuousSMul ℝ F] (c : ℝ)
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
      (isPiecewiseAffineOn_continuousAffineMap (0 : E →ᴬ[ℝ] F) V).congr fun _ _ => rfl
    simpa only [Finset.sum_empty] using h0
  | @insert a s has ih =>
    rw [Finset.sum_insert has]
    exact (hφ a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hφ i (Finset.mem_insert_of_mem hi))

end TauCeti

namespace Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A finite maximum of continuous affine functionals is piecewise affine on the whole space. -/
theorem isPiecewiseAffineOn_supAffine {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) :
    TauCeti.IsPiecewiseAffineOn (fun x => s.sup' hs (fun i => f i x)) (Set.univ : Set E) := by
  have hneg : (fun x => s.sup' hs (fun i => f i x)) =
      -(fun x => s.inf' hs (fun i => (-f i) x)) := by
    funext x
    dsimp only [Pi.neg_apply]
    apply le_antisymm
    · refine Finset.sup'_le hs _ fun i hi => le_neg.mp ?_
      exact Finset.inf'_le (fun j => (-f j) x) hi
    · refine neg_le.mp (Finset.le_inf' hs _ fun i hi => neg_le.mp ?_)
      simpa only [ContinuousAffineMap.neg_apply, neg_neg] using
        Finset.le_sup' (fun j => f j x) hi
  rw [hneg]
  exact (s.isPiecewiseAffineOn_infAffine hs (fun i => -f i)).neg

/-- A finite maximum of continuous affine functionals is piecewise linear on the whole source. -/
theorem isPLOn_supAffine {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) :
    TauCeti.IsPLOn (fun x => s.sup' hs (fun i => f i x)) (Set.univ : Set E) :=
  (s.isPiecewiseAffineOn_supAffine hs f).isPLOn

end Finset

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {V : Set E}

/-- Pointwise maximum of two coordinates on `ℝ × ℝ` is piecewise affine on the whole plane. -/
theorem isPiecewiseAffineOn_max_prod :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => max p.1 p.2) (Set.univ : Set (ℝ × ℝ)) := by
  let f : Bool → (ℝ × ℝ) →ᴬ[ℝ] ℝ := fun b =>
    cond b (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hsup := Finset.univ.isPiecewiseAffineOn_supAffine Finset.univ_nonempty f
  refine hsup.congr fun p _ => le_antisymm ?_ ?_
  · exact max_le (Finset.le_sup' (fun b => f b p) (Finset.mem_univ true))
      (Finset.le_sup' (fun b => f b p) (Finset.mem_univ false))
  · refine Finset.sup'_le Finset.univ_nonempty _ ?_
    rintro (_ | _) _
    · exact le_max_right p.1 p.2
    · exact le_max_left p.1 p.2

/-- Pointwise maximum of two real-valued piecewise-affine maps is piecewise affine. -/
theorem IsPiecewiseAffineOn.sup {f g : E → ℝ} (hf : IsPiecewiseAffineOn f V)
    (hg : IsPiecewiseAffineOn g V) : IsPiecewiseAffineOn (f ⊔ g) V :=
  isPiecewiseAffineOn_max_prod.comp (hf.prodMk hg) (mapsTo_univ _ _)

/-- Pointwise minimum of two real-valued piecewise-affine maps is piecewise affine. -/
theorem IsPiecewiseAffineOn.inf {f g : E → ℝ} (hf : IsPiecewiseAffineOn f V)
    (hg : IsPiecewiseAffineOn g V) : IsPiecewiseAffineOn (f ⊓ g) V := by
  have hinf : f ⊓ g = -((-f) ⊔ (-g)) := by
    funext x
    simp only [Pi.inf_apply, Pi.neg_apply, Pi.sup_apply]
    rcases le_total (f x) (g x) with h | h <;> simp [h]
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
theorem IsPiecewiseAffineOn.finset_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {φ : ι → E → ℝ} (hφ : ∀ i ∈ s, IsPiecewiseAffineOn (φ i) V) :
    IsPiecewiseAffineOn (fun x => s.sup' hs (fun i => φ i x)) V := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa only [Finset.sup'_singleton] using hφ a (Finset.mem_singleton_self a)
  | cons a s has hs ih =>
    have hfun : (fun x => (Finset.cons a s has).sup' (Finset.cons_nonempty has) (fun i => φ i x)) =
        φ a ⊔ (fun x => s.sup' hs (fun i => φ i x)) := by
      funext x
      exact Finset.sup'_cons (f := fun i => φ i x) hs
    rw [hfun]
    exact (hφ a (Finset.mem_cons_self a s)).sup
      (ih fun i hi => hφ i (Finset.mem_cons_of_mem hi))

/-- A finite pointwise minimum of real-valued piecewise-affine maps is piecewise affine. -/
theorem IsPiecewiseAffineOn.finset_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {φ : ι → E → ℝ} (hφ : ∀ i ∈ s, IsPiecewiseAffineOn (φ i) V) :
    IsPiecewiseAffineOn (fun x => s.inf' hs (fun i => φ i x)) V := by
  have hneg : (fun x => s.inf' hs (fun i => φ i x)) =
      -(fun x => s.sup' hs (fun i => (-φ i) x)) := by
    funext x
    dsimp only [Pi.neg_apply]
    apply le_antisymm
    · refine le_neg.mp (Finset.sup'_le hs _ fun i hi => ?_)
      simp only [neg_le_neg_iff]
      exact Finset.inf'_le (fun j => φ j x) hi
    · refine Finset.le_inf' hs _ fun i hi => neg_le.mp ?_
      exact Finset.le_sup' (fun k => -φ k x) hi
  rw [hneg]
  exact (IsPiecewiseAffineOn.finset_sup' s hs fun i hi => (hφ i hi).neg).neg

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

private theorem dense_setOf_continuousAffineMap_ne_zero [ContinuousAdd E] [ContinuousSMul ℝ E]
    {g : E →ᴬ[ℝ] ℝ} (hg : g ≠ 0) : Dense {x : E | g x ≠ 0} := by
  have hex : ∃ y : E, g y ≠ 0 := by
    by_contra! h
    exact hg (ContinuousAffineMap.ext h)
  obtain ⟨y, hy⟩ := hex
  rw [dense_iff_closure_eq]
  refine eq_univ_of_forall fun x => ?_
  by_cases hx : g x ≠ 0
  · exact subset_closure hx
  · rw [not_not] at hx
    let γ : ℝ → E := fun t => (1 - t) • x + t • y
    have hγ_cont : Continuous γ := by fun_prop
    have hγ0 : γ 0 = x := by simp [γ]
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ {z : E | g z ≠ 0} := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hval : g (γ t) = (1 - t) * g x + t * g y := by
        simpa [γ] using
          Convex.combo_affine_apply (f := g.toAffineMap) (a := 1 - t) (b := t) (by ring)
      rw [hval, hx, mul_zero, zero_add]
      exact mul_ne_zero ht.ne' hy
    have htend : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      rw [← hγ0]
      exact hγ_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto htend hmem

omit [AddCommGroup E] [Module ℝ E] in
private theorem dense_iInter_finset_of_isOpen {α : Type*} (s : Finset α) (U : α → Set E)
    (ho : ∀ a ∈ s, IsOpen (U a)) (hd : ∀ a ∈ s, Dense (U a)) :
    Dense (⋂ a ∈ s, U a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dense_univ]
  | @insert a s _has ih =>
    have heq : (⋂ b ∈ insert a s, U b) = U a ∩ ⋂ b ∈ s, U b := by
      ext x
      simp
    rw [heq]
    exact (hd a (Finset.mem_insert_self a s)).inter_of_isOpen_left
      (ih (fun b hb => ho b (Finset.mem_insert_of_mem hb))
        (fun b hb => hd b (Finset.mem_insert_of_mem hb)))
      (ho a (Finset.mem_insert_self a s))

private theorem eqOn_of_isConnected_of_forall_mem {U : Set E} (hU : IsConnected U)
    {f : E → ℝ} (hf : Continuous f) (S : Finset (E →ᴬ[ℝ] ℝ))
    (hmem : ∀ x ∈ U, ∃ a ∈ S, f x = a x)
    (hsep : ∀ x ∈ U, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a x ≠ b x) :
    ∃ a ∈ S, EqOn f a U := by
  classical
  obtain ⟨x₀, hx₀⟩ := hU.nonempty
  obtain ⟨a₀, ha₀, hfx₀⟩ := hmem x₀ hx₀
  refine ⟨a₀, ha₀, ?_⟩
  let T : Set E := {x | f x = a₀ x}
  let T' : Set E := ⋃ b ∈ S.erase a₀, {x : E | f x = b x}
  have hT_closed : IsClosed T := isClosed_eq hf a₀.continuous
  have hT'_closed : IsClosed T' :=
    (S.erase a₀).finite_toSet.isClosed_biUnion fun b _ => isClosed_eq hf b.continuous
  have hU_sub : U ⊆ T ∪ T' := by
    intro x hx
    obtain ⟨b, hbS, hfb⟩ := hmem x hx
    by_cases hba : b = a₀
    · exact Or.inl (by simp [T, hfb, hba])
    · exact Or.inr (mem_iUnion₂.mpr ⟨b, Finset.mem_erase.mpr ⟨hba, hbS⟩, hfb⟩)
  intro y hy
  by_contra hne
  obtain ⟨b, hbS, hfb⟩ := hmem y hy
  have hba : b ≠ a₀ := fun h => hne (h ▸ hfb)
  have hyT' : y ∈ T' := mem_iUnion₂.mpr ⟨b, Finset.mem_erase.mpr ⟨hba, hbS⟩, hfb⟩
  obtain ⟨z, hzU, hzT, hzT'⟩ := isPreconnected_closed_iff.mp hU.isPreconnected
    T T' hT_closed hT'_closed hU_sub ⟨x₀, hx₀, hfx₀⟩ ⟨y, hy, hyT'⟩
  obtain ⟨c, hc, hfc⟩ := mem_iUnion₂.mp hzT'
  obtain ⟨hca, hcS⟩ := Finset.mem_erase.mp hc
  exact hsep z hzU c hcS a₀ ha₀ hca (hfc.symm.trans hzT)

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
      refine eqOn_of_isConnected_of_forall_mem
        ((TauCeti.Convex.convex_signCell g σ.val).isConnected σ.property.2) hf S
        (fun x _ => hmemS x) (fun x hx a ha b hb hab => ?_)
      have hne : g ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩⟩ x ≠ 0 := by
        have hsign := (TauCeti.Convex.mem_signCell.mp hx)
          ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩⟩
        rw [← sign_ne_zero, hsign]
        exact σ.property.1 _
      exact sub_ne_zero.mp hne
    choose piece _ hpiece_eq using hpiece
    refine isPiecewiseAffineOn_of_finite (ι := ι)
      (C := fun σ => closure (TauCeti.Convex.signCell g σ.val)) (A := piece)
      (fun σ => TauCeti.Convex.isConvexPolyhedron_closure_signCell) ?_
      (fun σ x hx => (hpiece_eq σ).closure hf (piece σ).continuous hx.2)
    have hdense_inter : Dense (⋂ p : D, {x : E | g p x ≠ 0}) := by
      have heq : (⋂ p : D, {x : E | g p x ≠ 0}) =
          ⋂ p ∈ Finset.univ, {x : E | g p x ≠ 0} := by
        simp
      rw [heq]
      refine dense_iInter_finset_of_isOpen Finset.univ _
        (fun p _ => isOpen_ne_fun (g p).continuous continuous_const) (fun p _ => ?_)
      refine dense_setOf_continuousAffineMap_ne_zero
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
