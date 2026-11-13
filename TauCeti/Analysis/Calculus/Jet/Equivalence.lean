/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Equality of finite jets in nonlinear bundle coordinates

`TauCeti.SameJetAt` means equality of values and all Fréchet derivatives through a
specified finite order. The composition theorem uses Mathlib's Faà di Bruno formula;
in particular it retains all derivatives of nonlinear coordinate changes.

For local sections, `SameJetAt.coordChange` treats simultaneous base changes and
base-dependent nonlinear fibre changes. The converse, `sameJetAt_coordChange_iff`,
uses inverse changes defined only as germs. Thus equality of finite jets of smooth
local sections is independent of the bundle coordinates. Over `ℝ` or `ℂ`, the
derivatives of a `C^n` map through order `n` are symmetric multilinear maps: ordered
arguments are evaluations of one derivative, not independent jet coordinates.
Over a general nontrivially normed field, the results compare `iteratedFDeriv`
directly and do not require symmetry.

This file concerns equivalence of local sections in charts. It does not construct
the global jet bundle, its smooth atlas, or realization of prescribed derivative tuples.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A.
* Kolář, Michor and Slovák, *Natural Operations in Differential Geometry*, Chapter 12.
-/

public section

open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 E E' F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Two maps have the same finite jet at a point if their derivatives, including
order zero (the value), agree through the specified order. Smoothness is imposed
separately by the calculus theorems. -/
def SameJetAt (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (x : E) (f g : E → F) : Prop :=
  ∀ i, i ≤ n → iteratedFDeriv 𝕜 i f x = iteratedFDeriv 𝕜 i g x

/-- The derivative characterization of equality of finite jets. -/
@[grind =]
theorem sameJetAt_iff {n : ℕ} {f g : E → F} {x : E} :
    SameJetAt 𝕜 n x f g ↔
      ∀ i, i ≤ n → iteratedFDeriv 𝕜 i f x = iteratedFDeriv 𝕜 i g x := Iff.rfl

namespace SameJetAt

variable {n m : ℕ} {f f' : E → F} {g g' : F → G} {x : E}

/-- Equality of finite jets is reflexive. -/
@[refl, simp]
theorem refl (f : E → F) (x : E) : SameJetAt 𝕜 n x f f := fun _ _ ↦ rfl

/-- Equality of finite jets is symmetric. -/
@[symm]
theorem symm (h : SameJetAt 𝕜 n x f f') : SameJetAt 𝕜 n x f' f :=
  fun i hi ↦ (h i hi).symm

/-- Equality of finite jets is transitive. -/
@[trans]
theorem trans {f'' : E → F} (h : SameJetAt 𝕜 n x f f')
    (h' : SameJetAt 𝕜 n x f' f'') : SameJetAt 𝕜 n x f f'' :=
  fun i hi ↦ (h i hi).trans (h' i hi)

instance : Trans (SameJetAt 𝕜 n x (F := F)) (SameJetAt 𝕜 n x) (SameJetAt 𝕜 n x) :=
  ⟨trans⟩

/-- Equality of finite jets at a fixed point is an equivalence relation. -/
theorem equivalence : Equivalence (SameJetAt 𝕜 n x (F := F)) :=
  ⟨fun f ↦ refl f x, symm, trans⟩

variable (𝕜 F) in
/-- The setoid identifying maps with the same finite jet at a fixed point. -/
def setoid (n : ℕ) (x : E) : Setoid (E → F) where
  r := SameJetAt 𝕜 n x
  iseqv := equivalence

/-- The finite-jet setoid relates precisely maps with equal finite jets. -/
@[simp]
theorem setoid_apply : setoid 𝕜 F n x f f' ↔ SameJetAt 𝕜 n x f f' := (Iff.rfl)

/-- Truncation preserves equality of jets. -/
theorem of_le (h : SameJetAt 𝕜 n x f f') (hmn : m ≤ n) : SameJetAt 𝕜 m x f f' :=
  fun i hi ↦ h i (hi.trans hmn)

/-- Equal jets have equal derivatives through the specified order. -/
theorem iteratedFDeriv_eq (h : SameJetAt 𝕜 n x f f') {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i f x = iteratedFDeriv 𝕜 i f' x := h i hi

/-- Equal jets have equal field values, also at order zero. -/
@[grind →]
theorem apply_eq (h : SameJetAt 𝕜 n x f f') : f x = f' x := by
  have h0 := congrArg (fun A ↦ A (fun i : Fin 0 ↦ Fin.elim0 i)) (h 0 (Nat.zero_le n))
  simpa only [iteratedFDeriv_zero_apply] using h0

/-- Equal jets of positive order have equal first derivatives. -/
@[grind =>]
theorem fderiv_eq (h : SameJetAt 𝕜 n x f f') (hn : 1 ≤ n) :
    fderiv 𝕜 f x = fderiv 𝕜 f' x := by
  ext u
  simpa only [iteratedFDeriv_one_apply] using
    congrArg (fun A ↦ A (fun _ : Fin 1 ↦ u)) (h.iteratedFDeriv_eq hn)

/-- Taking the derivative lowers the order of equal jets by one. -/
theorem fderiv (h : SameJetAt 𝕜 (n + 1) x f f') :
    SameJetAt 𝕜 n x (fderiv 𝕜 f) (fderiv 𝕜 f') := by
  intro i hi
  apply (continuousMultilinearCurryRightEquiv' 𝕜 i E F).symm.injective
  simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply] using
    h.iteratedFDeriv_eq (Nat.succ_le_succ hi)

/-- Post-composition by a continuous linear equivalence preserves equality of jets,
without differentiability assumptions. -/
theorem continuousLinearEquiv_comp (h : SameJetAt 𝕜 n x f f') (e : F ≃L[𝕜] G) :
    SameJetAt 𝕜 n x (e ∘ f) (e ∘ f') := by
  intro i hi
  simp only [ContinuousLinearEquiv.iteratedFDeriv_comp_left, h.iteratedFDeriv_eq hi]

/-- Post-composition by a linear isometry equivalence preserves equality of jets,
without differentiability assumptions. -/
theorem linearIsometryEquiv_comp (h : SameJetAt 𝕜 n x f f') (e : F ≃ₗᵢ[𝕜] G) :
    SameJetAt 𝕜 n x (e ∘ f) (e ∘ f') := by
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    h.continuousLinearEquiv_comp e.toContinuousLinearEquiv

/-- Taking `m` derivatives lowers the order of equal jets by `m`.
No differentiability assumption is needed. -/
theorem iteratedFDeriv (h : SameJetAt 𝕜 (n + m) x f f') :
    SameJetAt 𝕜 n x (iteratedFDeriv 𝕜 m f) (iteratedFDeriv 𝕜 m f') := by
  induction m generalizing n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    exact h.linearIsometryEquiv_comp (continuousMultilinearCurryFin0 𝕜 E F).symm
  | succ m ih =>
    have hd := (ih (n := n + 1) (by simpa only [Nat.add_right_comm, Nat.add_assoc] using h)).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    exact hd.linearIsometryEquiv_comp
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) ↦ E) F).symm

/-- The jet depends only on the germ of a local section. -/
theorem _root_.Filter.EventuallyEq.sameJetAt (h : f =ᶠ[𝓝 x] f') : SameJetAt 𝕜 n x f f' :=
  fun i _ ↦ (h.iteratedFDeriv 𝕜 i).eq_of_nhds

/-- Equality of jets is unchanged by choosing other extensions of the local sections. -/
theorem congr {a b : E → F} (h : SameJetAt 𝕜 n x f f')
    (ha : f =ᶠ[𝓝 x] a) (hb : f' =ᶠ[𝓝 x] b) : SameJetAt 𝕜 n x a b :=
  ha.sameJetAt.symm.trans (h.trans hb.sameJetAt)

/-- The finite jet of a composite depends only on the two finite jets being composed. -/
theorem comp (hf : SameJetAt 𝕜 n x f f') (hg : SameJetAt 𝕜 n (f x) g g')
    (hcf : ContDiffAt 𝕜 n f x) (hcf' : ContDiffAt 𝕜 n f' x)
    (hcg : ContDiffAt 𝕜 n g (f x)) (hcg' : ContDiffAt 𝕜 n g' (f' x)) :
    SameJetAt 𝕜 n x (g ∘ f) (g' ∘ f') := by
  intro i hi
  rw [iteratedFDeriv_comp hcg hcf (by exact_mod_cast hi),
    iteratedFDeriv_comp hcg' hcf' (by exact_mod_cast hi), ← hf.apply_eq]
  simp only [FormalMultilinearSeries.taylorComp]
  apply Finset.sum_congr rfl
  intro c _
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeries]
  rw [hg c.length (c.length_le.trans hi)]
  congr 1
  funext j
  exact hf (c.partSize j) ((c.partSize_le j).trans hi)

/-- Projection to the first component preserves equality of finite jets. -/
theorem fst {a a' : E → F × G} (h : SameJetAt 𝕜 n x a a')
    (hca : ContDiffAt 𝕜 n a x) (hca' : ContDiffAt 𝕜 n a' x) :
    SameJetAt 𝕜 n x (fun y ↦ (a y).1) (fun y ↦ (a' y).1) := by
  simpa only [Function.comp_def] using
    h.comp (refl Prod.fst _) hca hca' contDiffAt_fst contDiffAt_fst

/-- Projection to the second component preserves equality of finite jets. -/
theorem snd {a a' : E → F × G} (h : SameJetAt 𝕜 n x a a')
    (hca : ContDiffAt 𝕜 n a x) (hca' : ContDiffAt 𝕜 n a' x) :
    SameJetAt 𝕜 n x (fun y ↦ (a y).2) (fun y ↦ (a' y).2) := by
  simpa only [Function.comp_def] using
    h.comp (refl Prod.snd _) hca hca' contDiffAt_snd contDiffAt_snd

/-- Pairing sections preserves equality of finite jets. -/
theorem prodMk {a a' : E → G} (hf : SameJetAt 𝕜 n x f f')
    (ha : SameJetAt 𝕜 n x a a')
    (hcf : ContDiffAt 𝕜 n f x) (hcf' : ContDiffAt 𝕜 n f' x)
    (hca : ContDiffAt 𝕜 n a x) (hca' : ContDiffAt 𝕜 n a' x) :
    SameJetAt 𝕜 n x (fun y ↦ (f y, a y)) (fun y ↦ (f' y, a' y)) := by
  intro i hi
  rw [iteratedFDeriv_prodMk hcf hca (by exact_mod_cast hi),
    iteratedFDeriv_prodMk hcf' hca' (by exact_mod_cast hi), hf i hi, ha i hi]

/-- A base change and a base-dependent nonlinear fibre change preserve equality of
finite jets of local sections. No linearity in the fibre is assumed. -/
theorem coordChange {h : E' → E} {a : E' × F → G} {y : E'}
    (hf : SameJetAt 𝕜 n (h y) f f')
    (hcf : ContDiffAt 𝕜 n f (h y)) (hcf' : ContDiffAt 𝕜 n f' (h y))
    (hh : ContDiffAt 𝕜 n h y) (ha : ContDiffAt 𝕜 n a (y, f (h y))) :
    SameJetAt 𝕜 n y (fun z ↦ a (z, f (h z))) (fun z ↦ a (z, f' (h z))) := by
  have hp := (refl h y).comp hf hh hh hcf hcf'
  have hpair := (refl (id : E' → E') y).prodMk hp
    contDiffAt_id contDiffAt_id (hcf.comp y hh) (hcf'.comp y hh)
  exact hpair.comp (refl a _) (contDiffAt_id.prodMk (hcf.comp y hh))
    (contDiffAt_id.prodMk (hcf'.comp y hh)) ha
    (by simpa only [hf.apply_eq, Function.comp_apply, id_eq] using ha)

end SameJetAt

/-- Post-composition by a continuous linear equivalence preserves and reflects equality
of finite jets, without differentiability assumptions. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_sameJetAt_iff (e : F ≃L[𝕜] G)
    {n : ℕ} {x : E} {f f' : E → F} :
    SameJetAt 𝕜 n x (e ∘ f) (e ∘ f') ↔ SameJetAt 𝕜 n x f f' := by
  constructor
  · intro h
    simpa only [Function.comp_def, e.symm_apply_apply] using
      h.continuousLinearEquiv_comp e.symm
  · exact fun h ↦ h.continuousLinearEquiv_comp e

/-- Post-composition by a linear isometry equivalence preserves and reflects equality
of finite jets, without differentiability assumptions. -/
@[simp]
theorem _root_.LinearIsometryEquiv.comp_sameJetAt_iff (e : F ≃ₗᵢ[𝕜] G)
    {n : ℕ} {x : E} {f f' : E → F} :
    SameJetAt 𝕜 n x (e ∘ f) (e ∘ f') ↔ SameJetAt 𝕜 n x f f' := by
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    e.toContinuousLinearEquiv.comp_sameJetAt_iff (n := n) (x := x) (f := f) (f' := f')

/-- Jets of product-valued maps agree exactly when their component jets agree. -/
theorem sameJetAt_prod_iff {n : ℕ} {a a' : E → F × G} {x : E}
    (hca : ContDiffAt 𝕜 n a x) (hca' : ContDiffAt 𝕜 n a' x) :
    SameJetAt 𝕜 n x a a' ↔
      SameJetAt 𝕜 n x (fun y ↦ (a y).1) (fun y ↦ (a' y).1) ∧
      SameJetAt 𝕜 n x (fun y ↦ (a y).2) (fun y ↦ (a' y).2) := by
  constructor
  · intro h
    exact ⟨h.fst hca hca', h.snd hca hca'⟩
  · rintro ⟨hf, hg⟩
    exact hf.prodMk hg hca.fst hca'.fst hca.snd hca'.snd

/-- Jets of paired maps agree exactly when the two component jets agree. -/
@[simp]
theorem sameJetAt_prodMk_iff {n : ℕ} {f f' : E → F} {a a' : E → G} {x : E}
    (hcf : ContDiffAt 𝕜 n f x) (hcf' : ContDiffAt 𝕜 n f' x)
    (hca : ContDiffAt 𝕜 n a x) (hca' : ContDiffAt 𝕜 n a' x) :
    SameJetAt 𝕜 n x (fun y ↦ (f y, a y)) (fun y ↦ (f' y, a' y)) ↔
      SameJetAt 𝕜 n x f f' ∧ SameJetAt 𝕜 n x a a' :=
  sameJetAt_prod_iff (hcf.prodMk hca) (hcf'.prodMk hca')

/-- Constant sections have equal finite jets exactly when their values agree. -/
@[to_fun (attr := simp)]
theorem sameJetAt_const_iff {n : ℕ} {c d : F} {x : E} :
    SameJetAt 𝕜 n x (Function.const E c) (Function.const E d) ↔ c = d :=
  ⟨SameJetAt.apply_eq, fun h ↦ h ▸ SameJetAt.refl _ _⟩

/-- Equality of finite jets is unchanged by exchanging the two maps. -/
theorem sameJetAt_comm {n : ℕ} {f g : E → F} {x : E} :
    SameJetAt 𝕜 n x f g ↔ SameJetAt 𝕜 n x g f :=
  ⟨SameJetAt.symm, SameJetAt.symm⟩

/-- Equality of finite jets depends only on the germs of the two maps. -/
theorem sameJetAt_congr {n : ℕ} {f g a b : E → F} {x : E}
    (ha : f =ᶠ[𝓝 x] a) (hb : g =ᶠ[𝓝 x] b) :
    SameJetAt 𝕜 n x f g ↔ SameJetAt 𝕜 n x a b :=
  ⟨fun h ↦ h.congr ha hb, fun h ↦ h.congr ha.symm hb.symm⟩

/-- An order-zero jet records exactly the field value. -/
@[simp, grind =]
theorem sameJetAt_zero_iff {f g : E → F} {x : E} : SameJetAt 𝕜 0 x f g ↔ f x = g x := by
  constructor
  · exact SameJetAt.apply_eq
  · intro h i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    ext v
    simp only [iteratedFDeriv_zero_apply, h]

/-- Equality of successor-order jets amounts to equality of the lower jets and
of the top derivatives. -/
@[grind =]
theorem sameJetAt_succ_iff {n : ℕ} {f g : E → F} {x : E} :
    SameJetAt 𝕜 (n + 1) x f g ↔ SameJetAt 𝕜 n x f g ∧
      iteratedFDeriv 𝕜 (n + 1) f x = iteratedFDeriv 𝕜 (n + 1) g x := by
  constructor
  · intro h
    exact ⟨h.of_le (Nat.le_succ n), h.iteratedFDeriv_eq le_rfl⟩
  · rintro ⟨h, htop⟩ i hi
    by_cases hin : i ≤ n
    · exact h.iteratedFDeriv_eq hin
    · have : i = n + 1 := by omega
      subst i
      exact htop

/-- Equality of successor-order jets is equality of values and of the jets of
the derivative maps. No differentiability assumption is needed. -/
theorem sameJetAt_succ_iff_fderiv {n : ℕ} {f g : E → F} {x : E} :
    SameJetAt 𝕜 (n + 1) x f g ↔
      f x = g x ∧ SameJetAt 𝕜 n x (fderiv 𝕜 f) (fderiv 𝕜 g) := by
  constructor
  · intro h
    exact ⟨h.apply_eq, h.fderiv⟩
  · rintro ⟨hval, hd⟩ i hi
    cases i with
    | zero =>
      ext v
      simp only [iteratedFDeriv_zero_apply, hval]
    | succ i =>
      simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        hd.iteratedFDeriv_eq (Nat.le_of_succ_le_succ hi)]

/-- A first-order jet records exactly the value and the first derivative. -/
@[simp, grind =]
theorem sameJetAt_one_iff {f g : E → F} {x : E} :
    SameJetAt 𝕜 1 x f g ↔ f x = g x ∧ fderiv 𝕜 f x = fderiv 𝕜 g x := by
  rw [sameJetAt_succ_iff_fderiv, sameJetAt_zero_iff]

/-- Equality of finite jets is independent of smooth bundle coordinates. Assume
`C^n` regularity at the displayed points, `k (h y) = y`, and the base inverse germ
`h ∘ k =ᶠ[𝓝 (h y)] id`. The same `b` is a left-inverse germ near
`(h y, f (h y))`; the fibre change must also distinguish the two field values at
`y` as expressed by `hinj`. No global inverse or fibre-linearity is required. -/
theorem sameJetAt_coordChange_iff {n : ℕ} {h : E' → E} {k : E → E'}
    {a : E' × F → G} {b : E × G → F} {f f' : E → F} {y : E'}
    (hcf : ContDiffAt 𝕜 n f (h y)) (hcf' : ContDiffAt 𝕜 n f' (h y))
    (hh : ContDiffAt 𝕜 n h y) (hk : ContDiffAt 𝕜 n k (h y))
    (ha : ContDiffAt 𝕜 n a (y, f (h y)))
    (hb : ContDiffAt 𝕜 n b (h y, a (y, f (h y))))
    (hbase : h ∘ k =ᶠ[𝓝 (h y)] id) (hpoint : k (h y) = y)
    (hfibre : (fun p : E × F ↦ b (p.1, a (k p.1, p.2))) =ᶠ[𝓝 (h y, f (h y))] Prod.snd)
    (hinj : a (y, f (h y)) = a (y, f' (h y)) → f (h y) = f' (h y)) :
    SameJetAt 𝕜 n y (fun z ↦ a (z, f (h z))) (fun z ↦ a (z, f' (h z))) ↔
      SameJetAt 𝕜 n (h y) f f' := by
  constructor
  · intro hj
    have hval : f (h y) = f' (h y) := hinj hj.apply_eq
    have ha' : ContDiffAt 𝕜 n a (y, f' (h y)) := hval ▸ ha
    have hfibre' : (fun p : E × F ↦ b (p.1, a (k p.1, p.2)))
        =ᶠ[𝓝 (h y, f' (h y))] Prod.snd := hval ▸ hfibre
    have ht := hj
    rw [← hpoint] at ht
    have hback := ht.coordChange
      (by simpa only [hpoint, Function.comp_def, id_eq] using
        ha.comp y (contDiffAt_id.prodMk (hcf.comp y hh)))
      (by simpa only [hpoint, Function.comp_def, id_eq] using
        ha'.comp y (contDiffAt_id.prodMk (hcf'.comp y hh)))
      hk (by simpa only [hpoint] using hb)
    have recover (s : E → F) (hs : ContDiffAt 𝕜 n s (h y))
        (hinv : (fun p : E × F ↦ b (p.1, a (k p.1, p.2))) =ᶠ[𝓝 (h y, s (h y))] Prod.snd) :
        (fun z ↦ b (z, a (k z, s (h (k z))))) =ᶠ[𝓝 (h y)] s := by
      have hsbase : (fun z ↦ s (h (k z))) =ᶠ[𝓝 (h y)] s :=
        hbase.mono fun z hz ↦ congrArg s hz
      have hinv' := (continuousAt_id.prodMk hs.continuousAt).eventually hinv
      filter_upwards [hsbase, hinv'] with z hz hzi
      simpa only [hz, id_eq] using hzi
    exact hback.congr (recover f hcf hfibre) (recover f' hcf' hfibre')
  · intro hj
    exact hj.coordChange hcf hcf' hh ha

end TauCeti
