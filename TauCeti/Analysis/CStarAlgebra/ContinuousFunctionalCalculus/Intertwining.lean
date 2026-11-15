/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Intertwining operators through the continuous functional calculus

Let `X : E →L[𝕜] F` be a bounded operator between Hilbert spaces which intertwines operators
`a` on `E` and `b` on `F`, in the sense that `X a = b X`, and which also intertwines their
adjoints. Then `X` intertwines every continuous function of `a` and `b`:

`X (f a) = (f b) X`.

Both `a` and `b` are evaluated on the compact set `spectrum a ∪ spectrum b`, where the
symbols satisfying this identity form a closed subalgebra containing the identity and its
conjugate. By the Stone–Weierstrass theorem this subalgebra is everything. This is the
two-space form of Mathlib's `Commute.cfc`, and the proof follows that of `Commute.cfcHom`.
The same argument in a single topological `⋆`-algebra shows that `SemiconjBy x a b` and
`SemiconjBy x (star a) (star b)` imply `SemiconjBy x (cfc f a) (cfc f b)`; in particular an
element `x` anticommuting with a self-adjoint `a` anticommutes with `cfc f a` for odd `f` and
commutes with `cfc f a` for even `f`.

For unitary operators the adjoint hypothesis is automatic, since the adjoint is the inverse;
more generally it suffices that `a` is a coisometry and `b` an isometry.
For normal operators it is the content of the Fuglede–Putnam–Rosenblum theorem, which Mathlib
proves as `SemiconjBy.star_right` for elements of a single C⋆-algebra.

## Main results

* `ContinuousLinearMap.comp_cfc_eq_cfc_comp`: an operator intertwining `a, b` and their adjoints
  intertwines `cfc f a` and `cfc f b`.
* `ContinuousLinearMap.comp_star_eq_star_comp_of_mul_star_self_of_star_mul_self`: an operator
  intertwining a coisometry and an isometry, in particular two unitaries, intertwines their
  adjoints.
* `SemiconjBy.cfc`, `IsSelfAdjoint.semiconjBy_cfc`: in a single topological `⋆`-algebra,
  semiconjugacy of `a, b` and their stars passes to `cfc f a` and `cfc f b`.
* `TauCeti.mul_cfc_of_mul_eq_neg_mul`, `TauCeti.mul_cfc_eq_neg_cfc_mul_of_odd`,
  `TauCeti.commute_cfc_of_mul_eq_neg_mul_of_even`: anticommutation `x * a = -(a * x)` passes
  through the real continuous functional calculus via `x * cfc f a = cfc (f ∘ Neg.neg) a * x`.

## References

* B. Fuglede, *A commutativity theorem for normal operators*, Proc. Nat. Acad. Sci. U.S.A. 36
  (1950), 35–40.
* C. R. Putnam, *On normal operators in Hilbert space*, Amer. J. Math. 73 (1951), 357–362.
-/

public section

open ContinuousMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Intertwining through the continuous functional calculus.** If `X` intertwines `a` and `b`
and also their adjoints, then it intertwines `cfc f a` and `cfc f b` for every symbol `f`
continuous on both spectra. -/
theorem comp_cfc_eq_cfc_comp {p : (E →L[𝕜] E) → Prop} {q : (F →L[𝕜] F) → Prop}
    [ContinuousFunctionalCalculus 𝕜 (E →L[𝕜] E) p]
    [ContinuousFunctionalCalculus 𝕜 (F →L[𝕜] F) q]
    (X : E →L[𝕜] F) {a : E →L[𝕜] E} {b : F →L[𝕜] F}
    (h : X ∘L a = b ∘L X) (h_star : X ∘L star a = star b ∘L X) (f : 𝕜 → 𝕜)
    (hfa : ContinuousOn f (spectrum 𝕜 a) := by cfc_cont_tac)
    (hfb : ContinuousOn f (spectrum 𝕜 b) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (hb : q b := by cfc_tac) :
    X ∘L cfc f a = cfc f b ∘L X := by
  -- Both calculi are read on continuous symbols on the common compact set `K`.
  set K := spectrum 𝕜 a ∪ spectrum 𝕜 b
  have hca := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) (p := p) a
  have hcb := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) (p := q) b
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hca.union hcb)
  let ιa : C(spectrum 𝕜 a, K) := ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩
  let ιb : C(spectrum 𝕜 b, K) := ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩
  let φa := (cfcHom ha).comp (ιa.compStarAlgHom' 𝕜 𝕜)
  let φb := (cfcHom hb).comp (ιb.compStarAlgHom' 𝕜 𝕜)
  have hφa : Continuous φa := (cfcHom_continuous ha).comp (continuous_precomp ιa)
  have hφb : Continuous φb := (cfcHom_continuous hb).comp (continuous_precomp ιb)
  have hφa_id : φa (.restrict K (.id 𝕜)) = a := by
    rw [← cfcHom_id (R := 𝕜) ha]
    exact congrArg (cfcHom ha) (ContinuousMap.ext fun _ => rfl)
  have hφb_id : φb (.restrict K (.id 𝕜)) = b := by
    rw [← cfcHom_id (R := 𝕜) hb]
    exact congrArg (cfcHom hb) (ContinuousMap.ext fun _ => rfl)
  -- The symbols on `K` intertwined by `X` contain the constants, the identity and its conjugate,
  -- and are closed under sums, products and limits, so by Stone–Weierstrass they are all symbols.
  have key (g : C(K, 𝕜)) : X ∘L φa g = φb g ∘L X := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      have hr : ContinuousMap.const K r = algebraMap 𝕜 C(K, 𝕜) r := by ext; simp
      simp [hr, Algebra.algebraMap_eq_smul_one, one_def]
    | id => rwa [hφa_id, hφb_id]
    | star_id => rwa [map_star, map_star, hφa_id, hφb_id]
    | add f g hf hg => rw [map_add, map_add, comp_add, add_comp, hf, hg]
    | mul f g hf hg =>
      rw [map_mul, map_mul, mul_def, mul_def, ← comp_assoc, hf, comp_assoc, hg, comp_assoc]
    | frequently g hg =>
      have hclosed : IsClosed {g : C(K, 𝕜) | X ∘L φa g = φb g ∘L X} :=
        isClosed_eq (by fun_prop) (by fun_prop)
      exact hclosed.closure_subset_iff.mpr subset_rfl (mem_closure_iff_frequently.mpr hg)
  -- `cfc f a` and `cfc f b` are the two calculi at the restriction of `f` to `K`.
  have hf : ContinuousOn f K :=
    hfa.union_of_isClosed hfb hca.isClosed hcb.isClosed
  have hfa' : cfc f a = φa ⟨_, hf.domRestrict⟩ := by
    rw [cfc_apply f a]
    exact congrArg (cfcHom ha) (ContinuousMap.ext fun _ => rfl)
  have hfb' : cfc f b = φb ⟨_, hf.domRestrict⟩ := by
    rw [cfc_apply f b]
    exact congrArg (cfcHom hb) (ContinuousMap.ext fun _ => rfl)
  rw [hfa', hfb', key]

/-- If `X` intertwines a coisometry `u` and an isometry `v`, then it also intertwines their
adjoints. In particular this holds for unitaries `u` and `v`. -/
theorem comp_star_eq_star_comp_of_mul_star_self_of_star_mul_self (X : E →L[𝕜] F)
    {u : E →L[𝕜] E} {v : F →L[𝕜] F} (hu : u * star u = 1) (hv : star v * v = 1)
    (h : X ∘L u = v ∘L X) : X ∘L star u = star v ∘L X :=
  calc X ∘L star u = (star v * v) ∘L X ∘L star u := by rw [hv, one_def, id_comp]
    _ = star v ∘L X ∘L (u * star u) := by
        rw [mul_def, mul_def, comp_assoc, ← comp_assoc v, ← h, comp_assoc]
    _ = star v ∘L X := by rw [hu, one_def, comp_id]

end ContinuousLinearMap

section SemiconjBy

variable {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
  [TopologicalSpace A] [ContinuousFunctionalCalculus 𝕜 A p] [IsSemitopologicalRing A] [T2Space A]

/-- If `x` semiconjugates `a` to `b` (`x * a = b * x`) and `star a` to `star b`, then `x`
semiconjugates `cfc f a` to `cfc f b` for every symbol `f` continuous on both spectra. -/
protected theorem SemiconjBy.cfc {x a b : A} (h : SemiconjBy x a b)
    (h_star : SemiconjBy x (star a) (star b)) (f : 𝕜 → 𝕜)
    (hfa : ContinuousOn f (spectrum 𝕜 a) := by cfc_cont_tac)
    (hfb : ContinuousOn f (spectrum 𝕜 b) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (hb : p b := by cfc_tac) :
    SemiconjBy x (cfc f a) (cfc f b) := by
  set K := spectrum 𝕜 a ∪ spectrum 𝕜 b
  have hca := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) (p := p) a
  have hcb := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) (p := p) b
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hca.union hcb)
  let ιa : C(spectrum 𝕜 a, K) := ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩
  let ιb : C(spectrum 𝕜 b, K) := ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩
  let φa := (cfcHom ha).comp (ιa.compStarAlgHom' 𝕜 𝕜)
  let φb := (cfcHom hb).comp (ιb.compStarAlgHom' 𝕜 𝕜)
  have hφa : Continuous φa := (cfcHom_continuous ha).comp (continuous_precomp ιa)
  have hφb : Continuous φb := (cfcHom_continuous hb).comp (continuous_precomp ιb)
  have hφa_id : φa (.restrict K (.id 𝕜)) = a := by
    rw [← cfcHom_id (R := 𝕜) ha]
    exact congrArg (cfcHom ha) (ContinuousMap.ext fun _ => rfl)
  have hφb_id : φb (.restrict K (.id 𝕜)) = b := by
    rw [← cfcHom_id (R := 𝕜) hb]
    exact congrArg (cfcHom hb) (ContinuousMap.ext fun _ => rfl)
  have key (g : C(K, 𝕜)) : SemiconjBy x (φa g) (φb g) := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      have hr : ContinuousMap.const K r = algebraMap 𝕜 C(K, 𝕜) r := by ext; simp
      rw [hr, AlgHomClass.commutes, AlgHomClass.commutes]
      simp [SemiconjBy, Algebra.algebraMap_eq_smul_one]
    | id => rwa [hφa_id, hφb_id]
    | star_id => rwa [map_star, map_star, hφa_id, hφb_id]
    | add f g hf hg => rw [map_add, map_add]; exact hf.add_right hg
    | mul f g hf hg => rw [map_mul, map_mul]; exact hf.mul_right hg
    | frequently g hg =>
      have hclosed : IsClosed {g : C(K, 𝕜) | x * φa g = φb g * x} :=
        isClosed_eq (by fun_prop) (by fun_prop)
      exact hclosed.closure_subset_iff.mpr subset_rfl (mem_closure_iff_frequently.mpr hg)
  have hf : ContinuousOn f K := hfa.union_of_isClosed hfb hca.isClosed hcb.isClosed
  have hfa' : cfc f a = φa ⟨_, hf.domRestrict⟩ := by
    rw [cfc_apply f a]
    exact congrArg (cfcHom ha) (ContinuousMap.ext fun _ => rfl)
  have hfb' : cfc f b = φb ⟨_, hf.domRestrict⟩ := by
    rw [cfc_apply f b]
    exact congrArg (cfcHom hb) (ContinuousMap.ext fun _ => rfl)
  rw [hfa', hfb']
  exact key _

/-- For self-adjoint `a` and `b`, `SemiconjBy x a b` passes to `SemiconjBy x (cfc f a) (cfc f b)`
without a separate star hypothesis. -/
protected theorem IsSelfAdjoint.semiconjBy_cfc {x a b : A} (ha' : IsSelfAdjoint a)
    (hb' : IsSelfAdjoint b) (h : SemiconjBy x a b) (f : 𝕜 → 𝕜)
    (hfa : ContinuousOn f (spectrum 𝕜 a) := by cfc_cont_tac)
    (hfb : ContinuousOn f (spectrum 𝕜 b) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) (hb : p b := by cfc_tac) :
    SemiconjBy x (cfc f a) (cfc f b) :=
  h.cfc (by rwa [ha'.star_eq, hb'.star_eq]) f hfa hfb ha hb

end SemiconjBy

namespace TauCeti

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [ContinuousMap.UniqueHom ℝ A]
  [IsSemitopologicalRing A] [T2Space A]

/-- **Anticommutation through the real continuous functional calculus.** If `x` anticommutes with
`a` (`x * a = -(a * x)`), then `x * cfc f a = cfc (fun t ↦ f (-t)) a * x` for every `f : ℝ → ℝ`
continuous on `spectrum ℝ a` and `spectrum ℝ (-a)`. -/
theorem mul_cfc_of_mul_eq_neg_mul {x a : A} (h : x * a = -(a * x)) (f : ℝ → ℝ)
    (hfa : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (hfa_neg : ContinuousOn f (spectrum ℝ (-a)) := by cfc_cont_tac) :
    x * cfc f a = cfc (fun t ↦ f (-t)) a * x := by
  by_cases ha : IsSelfAdjoint a
  · have hsemi : SemiconjBy x a (-a) := by rw [SemiconjBy, neg_mul, ← h]
    have hcfc : x * cfc f a = cfc f (-a) * x :=
      ha.semiconjBy_cfc ha.neg hsemi f hfa hfa_neg ha ha.neg
    have hneg_img : ContinuousOn f ((-·) '' spectrum ℝ a) := by
      rwa [Set.image_neg_eq_neg, spectrum.neg_eq]
    rw [hcfc, ← cfc_comp_neg (f := f) (a := a) hneg_img ha]
  · rw [cfc_apply_of_not_predicate a ha, cfc_apply_of_not_predicate a ha, mul_zero, zero_mul]

/-- If `x` anticommutes with `a` and `f : ℝ → ℝ` is odd, then `x` anticommutes with `cfc f a`. -/
theorem mul_cfc_eq_neg_cfc_mul_of_odd {x a : A} (h : x * a = -(a * x)) {f : ℝ → ℝ}
    (hf_odd : Function.Odd f) (hfa : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac) :
    x * cfc f a = -(cfc f a * x) := by
  have hfa_neg : ContinuousOn f (spectrum ℝ (-a)) :=
    ((hfa.comp continuous_neg.continuousOn fun t ht ↦
      Set.mem_neg.mp ((spectrum.neg_eq (R := ℝ) a).symm ▸ ht)).neg).congr fun t _ ↦ by
        simp [hf_odd t]
  rw [mul_cfc_of_mul_eq_neg_mul h f hfa hfa_neg, show (fun t ↦ f (-t)) = fun t ↦ -(f t) from
    funext hf_odd, cfc_neg, neg_mul]

/-- If `x` anticommutes with `a` and `f : ℝ → ℝ` is even, then `x` commutes with `cfc f a`. -/
theorem commute_cfc_of_mul_eq_neg_mul_of_even {x a : A} (h : x * a = -(a * x)) {f : ℝ → ℝ}
    (hf_even : Function.Even f) (hfa : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac) :
    Commute x (cfc f a) := by
  have hfa_neg : ContinuousOn f (spectrum ℝ (-a)) :=
    (hfa.comp continuous_neg.continuousOn fun t ht ↦
      Set.mem_neg.mp ((spectrum.neg_eq (R := ℝ) a).symm ▸ ht)).congr fun t _ ↦ by
        simp [hf_even t]
  exact mul_cfc_of_mul_eq_neg_mul h f hfa hfa_neg |>.trans
    (by rw [show (fun t ↦ f (-t)) = f from funext hf_even])

end TauCeti
