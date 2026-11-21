/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup

/-!
# The long exact homotopy sequence of a Kan fibration

Let `p : E ⟶ B` be a Kan fibration whose base `B` is a Kan complex, `e` a vertex of `E` over the
vertex `b` of `B`, and `F = SSet.fiber p b` the fiber of `p` over `b`, a Kan complex with base point
`e` (`SSet.fiber.basePoint`). Then `E` is a Kan complex too, and the homotopy groups of the three
form the long exact sequence

`⋯ → π (n + 1) B b → π n F e → π n E e → π n B b → ⋯ → π 0 E e → π 0 B b`

of groups in positive degrees and of pointed sets in degree `0`.

The connecting map `SSet.KanComplex.HomotopySequence.δ p he n : π (n + 1) B b → π n F e` is defined
by lifting. A pointed `(n + 1)`-simplex `s` of `B` lifts to a simplex of `E` whose faces other than
the `0`th are constant at `e`, by filling a horn `Λ[n + 1, 0]` along `p`; the `0`th face of the lift
lies in `F`, and `δ` sends the class of `s` to its class. Such a lift with prescribed `0`th face `t`
is a `SSet.KanComplex.HomotopySequence.DeltaStruct s t`, and `δ (mk s) = mk t` exactly when one
exists (`SSet.KanComplex.HomotopySequence.δ_mk_eq_mk_iff`). All proofs fill a single horn along `p`
and read off one face, using the combinatorial homotopy relation `SSet.PtSimplex.RelStruct₀`, which
characterizes equality in `π n` of a Kan complex in every degree (`SSet.KanComplex.π.mk_eq_mk_iff`).

## Main results

* `SSet.KanComplex.HomotopySequence.δ_eq_one_iff`: exactness at `π (n + 1) B b`.
* `SSet.KanComplex.HomotopySequence.map_fiber_ι_eq_one_iff`: exactness at `π n F e`.
* `SSet.KanComplex.HomotopySequence.map_eq_one_iff`: exactness at `π n E e`.
* `SSet.KanComplex.HomotopySequence.δHom`: in positive degrees the connecting map is a group
  homomorphism, for the group structures of `SSet.KanComplex.π.group`.

Exactness is stated as the kernel of each map, the preimage of the class of the constant simplex,
being the image of the previous one; in degree `0` this is exactness of pointed sets.

## References

The construction of the connecting map through lifts whose other faces are constant, and the
statements of exactness, follow the file `TopCatModelCategory/SSet/HomotopySequence.lean` of Joël
Riou's formalization [topcat-model-category](https://github.com/joelriou/topcat-model-category) of
the Kan–Quillen model structure. The proofs here are different: they use horn fillers and
`SSet.PtSimplex.RelStruct₀` throughout, instead of lifting homotopies `Δ[n] ⊗ Δ[1] ⟶ E`, and the
connecting map is only built from the `0`th face.

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Lemma I.7.3.
-/

public section

universe u

open CategoryTheory Simplicial HomotopicalAlgebra

namespace SSet

open modelCategoryQuillen

namespace KanComplex

namespace HomotopySequence

variable {E B : SSet.{u}} {p : E ⟶ B} {b : B _⦋0⦌} {e : E _⦋0⦌} {he : p.app _ e = b}

/-- For a pointed `(n + 1)`-simplex `s` of `B` and a pointed `n`-simplex `t` of the fiber of `p`
over `b`, a `DeltaStruct s t` is a lift of `s` to `E` whose `0`th face is `t` and whose other
faces are constant at `e`. The connecting map sends the class of `s` to the class of `t`. -/
structure DeltaStruct {n : ℕ} (s : B.PtSimplex (n + 1) b)
    (t : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he)) where
  /-- The lift of `s`. -/
  map : Δ[n + 1] ⟶ E
  map_comp : map ≫ p = s.map := by cat_disch
  δ_zero_map : stdSimplex.δ 0 ≫ map = t.map ≫ (fiber p b).ι := by cat_disch
  δ_succ_map (j : Fin (n + 1)) : stdSimplex.δ j.succ ≫ map = const e := by cat_disch

namespace DeltaStruct

attribute [reassoc (attr := simp)] map_comp δ_zero_map δ_succ_map

end DeltaStruct

/-- The faces of a face: `δ j ≫ δ 0 = δ 0 ≫ δ j.succ`. -/
@[reassoc]
private lemma δ_comp_δ_zero {n : ℕ} (j : Fin (n + 2)) :
    stdSimplex.{u}.δ j ≫ stdSimplex.δ 0 = stdSimplex.δ 0 ≫ stdSimplex.δ j.succ := by
  simpa using (stdSimplex.{u}.δ_comp_δ (Fin.zero_le j)).symm

/-- A family of `(n + 1)`-simplices indexed by the nonzero `j : Fin (n + 3)` whose faces other than
the `0`th are constant is compatible on the horn `Λ[n + 2, 0]`. -/
private lemma isCompatible_of_δ_succ {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}
    {f : ∀ j : Fin (n + 3), j ≠ 0 → (Δ[n + 1] ⟶ X)}
    (hf : ∀ j hj (l : Fin (n + 1)), stdSimplex.δ l.succ ≫ f j hj = const x) :
    horn.IsCompatible f := by
  have hf' (j hj) (m : Fin (n + 2)) (hm : m ≠ 0) : stdSimplex.δ m ≫ f j hj = const x := by
    obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero hm
    exact hf j hj l
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  rw [hf' j hj _ (fun h ↦ ?_), hf' k hk _ (fun h ↦ ?_)]
  · exact hj (by simpa using congrArg Fin.castSucc h)
  · rw [Fin.pred_eq_iff_eq_succ] at h
    subst h
    exact hj (Fin.ext (by simpa [Fin.lt_def] using hjk))

private lemma val_two {n : ℕ} : ((2 : Fin (n + 3)) : ℕ) = 2 := by
  simp

private lemma one_ne_two {n : ℕ} : (1 : Fin (n + 3)) ≠ 2 :=
  Fin.ne_of_val_ne (by rw [val_two]; simp)

private lemma two_ne_zero {n : ℕ} : (2 : Fin (n + 3)) ≠ 0 :=
  Fin.ne_of_val_ne (by rw [val_two]; simp)

private lemma one_lt {n : ℕ} {j : Fin (n + 2)} (h₀ : j ≠ 0) (h₁ : j ≠ 1) : 1 < j := by
  rcases j with ⟨j, hj⟩
  simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one] at h₀ h₁
  simp [Fin.lt_def]
  omega

private lemma two_lt {n : ℕ} {j : Fin (n + 3)} (h₀ : j ≠ 0) (h₁ : j ≠ 1) (h₂ : j ≠ 2) : 2 < j := by
  simp only [ne_eq, Fin.ext_iff, val_two, Fin.val_zero, Fin.val_one] at h₀ h₁ h₂
  rw [Fin.lt_def, val_two]
  omega

/-- The composite of the maps induced by the fiber inclusion and by `p` is trivial. -/
@[simp]
lemma map_map_fiber_ι {n : ℕ} (x : π n (fiber p b : SSet) (fiber.basePoint p he)) :
    π.map p he (π.map (fiber p b).ι (fiber.ι_app_basePoint p he) x) = 1 := by
  induction x with | mk t
  rw [π.map_mk, π.map_mk, π.one_def]
  congr 1
  ext : 1
  simp

variable [Fibration p]

variable (he) in
/-- Every pointed `(n + 1)`-simplex of `B` has a `DeltaStruct`: a lift to `E` whose faces other
than the `0`th are constant at `e`. -/
lemma exists_deltaStruct {n : ℕ} (s : B.PtSimplex (n + 1) b) :
    ∃ t : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he), Nonempty (DeltaStruct s t) := by
  have hf : horn.IsCompatible (i := (0 : Fin (n + 2))) fun _ _ ↦ (const e : Δ[n] ⟶ E) := by
    obtain _ | n := n
    · simp
    · exact isCompatible_of_δ_succ fun _ _ _ ↦ comp_const _ _
  obtain ⟨τ, hτ, hτp⟩ := hf.exists_lift p s.map (fun j _ ↦ by simp [he])
  refine ⟨{ map := fiber.lift (stdSimplex.δ 0 ≫ τ) p b (by simp [hτp]), comm := ?_ }, ⟨{
    map := τ
    δ_zero_map := (fiber.lift_ι _ _ _ _).symm
    δ_succ_map := fun j ↦ hτ j.succ (Fin.succ_ne_zero j) }⟩⟩
  rw [← cancel_mono (fiber p b).ι]
  obtain _ | n := n
  · exact boundary.hom_ext₀
  · refine boundary.hom_ext fun j ↦ ?_
    simp [δ_comp_δ_zero_assoc, hτ _ (Fin.succ_ne_zero j)]

/-- Two `DeltaStruct`s for pointed simplices related by `RelStruct · · 1` have fiber components
related by `RelStruct₀`: lift the `RelStruct` from the horn `Λ[n + 2, 0]` whose faces `1` and `2`
are the two lifts and whose other faces are constant, and take the `0`th face. -/
private lemma nonempty_relStruct₀ {n : ℕ} {s s' : B.PtSimplex (n + 1) b}
    {t t' : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he)} (h : DeltaStruct s t)
    (h' : DeltaStruct s' t') (r : s.RelStruct s' 1) : Nonempty (t.RelStruct₀ t') := by
  let f (j : Fin (n + 3)) (_ : j ≠ 0) : Δ[n + 1] ⟶ E :=
    if j = 1 then h.map else if j = 2 then h'.map else const e
  have hf₁ : f 1 (by simp) = h.map := by simp [f]
  have hf₂ : f 2 two_ne_zero = h'.map := by simp [f, one_ne_two.symm]
  have hf (j : Fin (n + 3)) (hj) (hj₁ : j ≠ 1) (hj₂ : j ≠ 2) : f j hj = const e := by
    simp [f, hj₁, hj₂]
  obtain ⟨Φ, hΦ, hΦp⟩ := (isCompatible_of_δ_succ (f := f) (x := e) fun j hj l ↦ by
    dsimp only [f]
    split_ifs <;> simp).exists_lift p r.map fun j hj ↦ by
      by_cases hj₁ : j = 1
      · subst hj₁
        simpa [hf₁] using r.δ_castSucc_map.symm
      by_cases hj₂ : j = 2
      · subst hj₂
        simpa [hf₂] using r.δ_succ_map.symm
      rw [hf j hj hj₁ hj₂, r.δ_map_of_gt j (by simpa using two_lt hj hj₁ hj₂), const_comp, he]
  have hΦ₀ : (stdSimplex.δ 0 ≫ Φ) ≫ p = const b := by
    rw [Category.assoc, hΦp, r.δ_map_of_lt 0 (by simp)]
  refine ⟨{
    map := fiber.lift (stdSimplex.δ 0 ≫ Φ) p b hΦ₀
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := fun j hj ↦ absurd hj (Fin.not_lt_zero _)
    δ_map_of_gt := fun j hj ↦ ?_ }⟩
  · rw [← cancel_mono (fiber p b).ι, Category.assoc, fiber.lift_ι, Fin.castSucc_zero,
      ← h.δ_zero_map, ← hf₁, ← hΦ 1 (by simp)]
    simpa using stdSimplex.δ_comp_δ_self_assoc (i := (0 : Fin (n + 2))) Φ
  · rw [← cancel_mono (fiber p b).ι, Category.assoc, fiber.lift_ι, Fin.succ_zero_eq_one,
      δ_comp_δ_zero_assoc, ← h'.δ_zero_map, hΦ _ (Fin.succ_ne_zero _)]
    simp [hf₂]
  · rw [← cancel_mono (fiber p b).ι, Category.assoc, fiber.lift_ι, δ_comp_δ_zero_assoc,
      hΦ _ (Fin.succ_ne_zero _), hf _ _ ?_ ?_]
    · simp
    all_goals exact Fin.ne_of_val_ne (by
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_zero, val_two, Fin.val_one] at hj ⊢
      omega)

/-- A lift along `p` of the reflexive `RelStruct s s 1` whose faces `0` and `1` are a
`RelStruct₀ t t'` and a `DeltaStruct s t`, and whose faces after `2` are constant. -/
private lemma exists_lift_of_relStruct₀ {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t t' : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he)} (h : DeltaStruct s t)
    (r : t.RelStruct₀ t') :
    ∃ Φ : Δ[n + 2] ⟶ E, Φ ≫ p = (PtSimplex.RelStruct.refl s 1).map ∧
      stdSimplex.δ 0 ≫ Φ = r.map ≫ (fiber p b).ι ∧ stdSimplex.δ 1 ≫ Φ = h.map ∧
      ∀ j : Fin (n + 3), 2 < j → stdSimplex.δ j ≫ Φ = const e := by
  let f (j : Fin (n + 3)) (_ : j ≠ 2) : Δ[n + 1] ⟶ E :=
    if j = 0 then r.map ≫ (fiber p b).ι else if j = 1 then h.map else const e
  have hf₀ : f 0 two_ne_zero.symm = r.map ≫ (fiber p b).ι := by simp [f]
  have hf₁ : f 1 one_ne_two = h.map := by simp [f]
  have hf (j : Fin (n + 3)) (hj) (hj₀ : j ≠ 0) (hj₁ : j ≠ 1) : f j hj = const e := by
    simp [f, hj₀, hj₁]
  have hcompat : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    by_cases hk₁ : k = 1
    · subst hk₁
      obtain rfl : j = 0 := Fin.ext (by simpa [Fin.lt_def] using hjk)
      have := r.δ_castSucc_map
      rw [Fin.castSucc_zero] at this
      simp [hf₀, hf₁, reassoc_of% this]
    have hk₂ : 2 < k := two_lt (Fin.ne_zero_of_lt hjk) hk₁ hk
    rw [hf k hk (Fin.ne_zero_of_lt hjk) hk₁, comp_const]
    have hk' : 1 < (k.pred (Fin.ne_zero_of_lt hjk)).val := by
      rw [Fin.lt_def, val_two] at hk₂
      simp only [Fin.val_pred]
      omega
    by_cases hj₀ : j = 0
    · subst hj₀
      rw [hf₀, r.δ_map_of_gt_assoc _ (by simpa [Fin.lt_def] using hk')]
      simp
    by_cases hj₁ : j = 1
    · subst hj₁
      obtain ⟨l, hl⟩ := Fin.eq_succ_of_ne_zero (i := k.pred (Fin.ne_zero_of_lt hjk))
        (fun h₀ ↦ by simp [h₀] at hk')
      rw [hf₁, hl, h.δ_succ_map]
    · rw [hf j hj hj₀ hj₁, comp_const]
  let K := PtSimplex.RelStruct.refl s 1
  obtain ⟨Φ, hΦ, hΦp⟩ := hcompat.exists_lift p K.map fun j hj ↦ by
    by_cases hj₀ : j = 0
    · subst hj₀
      rw [hf₀, Category.assoc, fiber_ι_comp, comp_const, K.δ_map_of_lt 0 (by simp)]
    by_cases hj₁ : j = 1
    · subst hj₁
      simpa [hf₁] using K.δ_castSucc_map.symm
    rw [hf j hj hj₀ hj₁, const_comp, he, K.δ_map_of_gt j (by simpa using two_lt hj₀ hj₁ hj)]
  refine ⟨Φ, hΦp, by rw [hΦ 0 two_ne_zero.symm, hf₀], by rw [hΦ 1 one_ne_two, hf₁], fun j hj ↦ ?_⟩
  rw [hΦ j hj.ne', hf j hj.ne' (Fin.ne_zero_of_lt hj) (Fin.ne_of_gt (lt_trans (by
    rw [Fin.lt_def, val_two]; simp) hj))]

/-- A `DeltaStruct s t` and a `RelStruct₀ t t'` give a `DeltaStruct s t'`, the face `2` of the
lift of `exists_lift_of_relStruct₀`. -/
private lemma nonempty_deltaStruct_of_relStruct₀ {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t t' : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he)} (h : DeltaStruct s t)
    (r : t.RelStruct₀ t') : Nonempty (DeltaStruct s t') := by
  obtain ⟨Φ, hΦp, hΦ₀, hΦ₁, hΦ⟩ := exists_lift_of_relStruct₀ h r
  refine ⟨{
    map := stdSimplex.δ 2 ≫ Φ
    map_comp := by simpa [hΦp] using (PtSimplex.RelStruct.refl s 1).δ_succ_map
    δ_zero_map := ?_
    δ_succ_map := fun j ↦ ?_ }⟩
  · have := stdSimplex.{u}.δ_comp_δ_assoc (n := n) (i := 0) (j := 1) (by simp) Φ
    simp only [Fin.succ_one_eq_two, Fin.castSucc_zero] at this
    rw [this, hΦ₀]
    simpa using r.δ_succ_map =≫ (fiber p b).ι
  · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · have := stdSimplex.{u}.δ_comp_δ_self_assoc (n := n) (i := 1) Φ
      simp only [Fin.castSucc_one, Fin.succ_one_eq_two] at this
      rw [Fin.succ_zero_eq_one, ← this, hΦ₁]
      simpa using h.δ_succ_map 0
    · have := stdSimplex.{u}.δ_comp_δ''_assoc (n := n) (i := 2) (j := j.succ.succ)
        (by rw [Fin.le_def, val_two]; simp) Φ
      rw [← this, hΦ _ (by rw [Fin.lt_def, val_two]; simp), comp_const]

variable [KanComplex B]

variable (p he) in
/-- The connecting map `π (n + 1) B b → π n F e` of the Kan fibration `p`, where `F` is the fiber
of `p` over `b`: the class of a pointed `(n + 1)`-simplex `s` of `B` is sent to the class of the
`0`th face of a lift of `s` to `E` whose other faces are constant at `e` (a `DeltaStruct`). -/
noncomputable def δ (n : ℕ) : π (n + 1) B b → π n (fiber p b : SSet) (fiber.basePoint p he) :=
  π.lift (fun s ↦ π.mk (exists_deltaStruct he s).choose) fun s s' h ↦ by
    obtain ⟨r⟩ := nonempty_relStruct₀ (exists_deltaStruct he s).choose_spec.some
      (exists_deltaStruct he s').choose_spec.some (h.relStruct₀.relStruct 1)
    exact (π.mk_eq_mk_of_homotopy r.homotopy).symm

/-- The connecting map sends the class of `s` to the class of `t` when there is a
`DeltaStruct s t`. -/
lemma δ_mk_eq_of_deltaStruct {n : ℕ} {s : B.PtSimplex (n + 1) b}
    {t : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he)} (h : DeltaStruct s t) :
    δ p he n (π.mk s) = π.mk t := by
  obtain ⟨r⟩ := nonempty_relStruct₀ h (exists_deltaStruct he s).choose_spec.some (.refl s 1)
  simp only [δ, π.lift_mk]
  exact π.mk_eq_mk_of_homotopy r.homotopy

/-- The connecting map sends the class of `s` to the class of `t` exactly when there is a
`DeltaStruct s t`. -/
lemma δ_mk_eq_mk_iff {n : ℕ} (s : B.PtSimplex (n + 1) b)
    (t : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he)) :
    δ p he n (π.mk s) = π.mk t ↔ Nonempty (DeltaStruct s t) := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ δ_mk_eq_of_deltaStruct h⟩
  obtain ⟨t₀, ⟨h₀⟩⟩ := exists_deltaStruct he s
  rw [δ_mk_eq_of_deltaStruct h₀, π.mk_eq_mk_iff] at h
  exact nonempty_deltaStruct_of_relStruct₀ h₀ h.some

/-- The connecting map sends the class of the constant simplex to the class of the constant
simplex. -/
@[simp]
lemma δ_one (n : ℕ) : δ p he n 1 = 1 :=
  δ_mk_eq_of_deltaStruct (t := .const) { map := const e }

/-- The connecting map vanishes on the classes coming from `E`. -/
@[simp]
lemma δ_map {n : ℕ} (x : π (n + 1) E e) : δ p he n (π.map p he x) = 1 := by
  induction x with | mk σ
  rw [π.map_mk]
  exact δ_mk_eq_of_deltaStruct (t := .const) { map := σ.map }

/-- The fiber inclusion kills the image of the connecting map. -/
@[simp]
lemma map_fiber_ι_δ {n : ℕ} (x : π (n + 1) B b) :
    π.map (fiber p b).ι (fiber.ι_app_basePoint p he) (δ p he n x) = 1 := by
  induction x with | mk s
  obtain ⟨t, ⟨h⟩⟩ := exists_deltaStruct he s
  rw [δ_mk_eq_of_deltaStruct h, π.map_mk, π.one_def]
  exact (π.mk_eq_mk_of_homotopy (PtSimplex.RelStruct₀.homotopy
    { map := h.map
      δ_castSucc_map := by simp
      δ_succ_map := by simpa using h.δ_succ_map 0
      δ_map_of_lt := fun j hj ↦ absurd hj (Fin.not_lt_zero _)
      δ_map_of_gt := fun j hj ↦ by
        obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
        exact h.δ_succ_map j })).symm

/-- Exactness at `π (n + 1) B b`: the kernel of the connecting map is the image of
`π (n + 1) E e`. -/
lemma δ_eq_one_iff {n : ℕ} (x : π (n + 1) B b) :
    δ p he n x = 1 ↔ ∃ y, π.map p he y = x := by
  refine ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact δ_map y⟩
  induction x with | mk s
  rw [π.one_def, δ_mk_eq_mk_iff] at hx
  obtain ⟨h⟩ := hx
  refine ⟨π.mk (PtSimplex.ofδ h.map fun j ↦ ?_), ?_⟩
  · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · simp
    · exact h.δ_succ_map j
  · rw [π.map_mk]
    congr 1
    ext : 1
    simp

/-- Exactness at `π n F e`, where `F` is the fiber of `p` over `b`: the kernel of the map induced by
the fiber inclusion is the image of the connecting map. -/
lemma map_fiber_ι_eq_one_iff {n : ℕ} (x : π n (fiber p b : SSet) (fiber.basePoint p he)) :
    π.map (fiber p b).ι (fiber.ι_app_basePoint p he) x = 1 ↔ ∃ y, δ p he n y = x := by
  refine ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact map_fiber_ι_δ y⟩
  have : KanComplex E := isFibrant_of_fibration p
  induction x with | mk t
  rw [π.map_mk, π.one_def, π.mk_eq_mk_iff] at hx
  obtain ⟨r⟩ := hx
  have hr₀ : stdSimplex.δ 0 ≫ r.map = t.map ≫ (fiber p b).ι := by simpa using r.δ_castSucc_map
  have hr (j : Fin (n + 1)) : stdSimplex.δ j.succ ≫ r.map = const e := by
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · simpa using r.δ_succ_map
    · exact r.δ_map_of_gt _ (by simp [Fin.lt_def])
  refine ⟨π.mk (PtSimplex.ofδ (r.map ≫ p) fun j ↦ ?_),
    δ_mk_eq_of_deltaStruct
      { map := r.map, map_comp := (PtSimplex.ofδ_map _ _).symm, δ_zero_map := hr₀,
        δ_succ_map := hr }⟩
  obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
  · simp [reassoc_of% hr₀]
  · simp [reassoc_of% (hr j), he]

omit [KanComplex B] in
variable (he) in
include he in
/-- A lift along `p` of an `(n + 1)`-simplex `H` of `B` whose face `0` is `σ ≫ p` and whose faces
after `1` are constant at `b`, with face `0` equal to `σ` and faces after `1` constant at `e`. -/
private lemma exists_lift_of_δ_zero {n : ℕ} (σ : E.PtSimplex n e) (H : Δ[n + 1] ⟶ B)
    (H₀ : stdSimplex.δ 0 ≫ H = σ.map ≫ p)
    (H₁ : ∀ j : Fin (n + 2), 1 < j → stdSimplex.δ j ≫ H = const b) :
    ∃ Φ : Δ[n + 1] ⟶ E, Φ ≫ p = H ∧ stdSimplex.δ 0 ≫ Φ = σ.map ∧
      ∀ j : Fin (n + 2), 1 < j → stdSimplex.δ j ≫ Φ = const e := by
  let f (j : Fin (n + 2)) (_ : j ≠ 1) : Δ[n] ⟶ E := if j = 0 then σ.map else const e
  have hf₀ : f 0 (by simp) = σ.map := by simp [f]
  have hf (j : Fin (n + 2)) (hj) (hj₀ : j ≠ 0) : f j hj = const e := by simp [f, hj₀]
  have hcompat : horn.IsCompatible f := by
    obtain _ | n := n
    · simp
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    rw [hf k hk (Fin.ne_zero_of_lt hjk), comp_const]
    by_cases hj₀ : j = 0
    · subst hj₀
      rw [hf₀, PtSimplex.δ_map]
    · rw [hf j hj hj₀, comp_const]
  obtain ⟨Φ, hΦ, hΦp⟩ := hcompat.exists_lift p H fun j hj ↦ by
    by_cases hj₀ : j = 0
    · subst hj₀
      rw [hf₀, H₀]
    · rw [hf j hj hj₀, const_comp, he, H₁ j (one_lt hj₀ hj)]
  exact ⟨Φ, hΦp, by rw [hΦ 0 (by simp), hf₀], fun j hj ↦ by
    rw [hΦ j hj.ne', hf j hj.ne' (Fin.ne_zero_of_lt hj)]⟩

/-- Exactness at `π n E e`: the kernel of the map induced by `p` is the image of the homotopy of
the fiber. -/
lemma map_eq_one_iff {n : ℕ} (x : π n E e) :
    π.map p he x = 1 ↔ ∃ y, π.map (fiber p b).ι (fiber.ι_app_basePoint p he) y = x := by
  refine ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact map_map_fiber_ι y⟩
  have : KanComplex E := isFibrant_of_fibration p
  induction x with | mk σ
  rw [π.map_mk, π.one_def, π.mk_eq_mk_iff] at hx
  obtain ⟨H⟩ := hx
  -- The face `1` of the lift of `H` lies in the fiber and is homotopic to `σ`.
  obtain ⟨Φ, hΦp, hΦ₀, hΦ⟩ := exists_lift_of_δ_zero he σ H.map (by simpa using H.δ_castSucc_map)
    fun j hj ↦ H.δ_map_of_gt j (by simpa using hj)
  have hΦ₁ : (stdSimplex.δ 1 ≫ Φ) ≫ p = const b := by
    rw [Category.assoc, hΦp]
    simpa using H.δ_succ_map
  let τ : (fiber p b : SSet).PtSimplex n (fiber.basePoint p he) :=
    { map := fiber.lift (stdSimplex.δ 1 ≫ Φ) p b hΦ₁
      comm := by
        rw [← cancel_mono (fiber p b).ι]
        obtain _ | n := n
        · exact boundary.hom_ext₀
        refine boundary.hom_ext fun j ↦ ?_
        simp only [boundary.ι_ι_assoc, Category.assoc, fiber.lift_ι, Subcomplex.ofSimplex_ι,
          comp_const, const_comp, fiber.ι_app_basePoint]
        obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
        · have := stdSimplex.{u}.δ_comp_δ_self_assoc (n := n) (i := 0) Φ
          simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at this
          rw [← this, hΦ₀, PtSimplex.δ_map]
        · have := stdSimplex.{u}.δ_comp_δ_assoc (n := n) (i := 1) (j := j.succ)
            (by simp [Fin.le_def]) Φ
          simp only [Fin.castSucc_one] at this
          rw [← this, hΦ _ (by simp [Fin.lt_def]), comp_const] }
  refine ⟨π.mk τ, ?_⟩
  rw [π.map_mk, eq_comm, π.mk_eq_mk_iff]
  exact ⟨{
    map := Φ
    δ_castSucc_map := by simpa using hΦ₀
    δ_succ_map := by simp [τ]
    δ_map_of_lt := fun j hj ↦ absurd hj (Fin.not_lt_zero _)
    δ_map_of_gt := fun j hj ↦ hΦ j (by simpa using hj) }⟩

omit [KanComplex B] in
/-- A lift along `p` of a `MulStruct s₀₁ s₁₂ s₀₂` whose faces `n + 1`, `n + 2` and `n + 3` are
`DeltaStruct`s for `s₁₂`, `s₀₂` and `s₀₁`, and whose other nonzero faces are constant. -/
private lemma exists_lift_of_mulStruct {n : ℕ} {s₀₁ s₁₂ s₀₂ : B.PtSimplex (n + 2) b}
    {t₀₁ t₁₂ t₀₂ : (fiber p b : SSet).PtSimplex (n + 1) (fiber.basePoint p he)}
    (hs : s₀₁.MulStruct s₁₂ s₀₂ (Fin.last (n + 1))) (h₀₁ : DeltaStruct s₀₁ t₀₁)
    (h₁₂ : DeltaStruct s₁₂ t₁₂) (h₀₂ : DeltaStruct s₀₂ t₀₂) :
    ∃ Φ : Δ[n + 3] ⟶ E, Φ ≫ p = hs.map ∧
      (∀ j : Fin (n + 4), j ≠ 0 → j.val ≤ n → stdSimplex.δ j ≫ Φ = const e) ∧
      (∀ j : Fin (n + 4), j.val = n + 1 → stdSimplex.δ j ≫ Φ = h₁₂.map) ∧
      (∀ j : Fin (n + 4), j.val = n + 2 → stdSimplex.δ j ≫ Φ = h₀₂.map) ∧
      (∀ j : Fin (n + 4), j.val = n + 3 → stdSimplex.δ j ≫ Φ = h₀₁.map) := by
  let f (j : Fin (n + 4)) (_ : j ≠ 0) : Δ[n + 2] ⟶ E :=
    if j.val = n + 1 then h₁₂.map else if j.val = n + 2 then h₀₂.map
      else if j.val = n + 3 then h₀₁.map else const e
  have hf₁₂ (j : Fin (n + 4)) (hj) (h : j.val = n + 1) : f j hj = h₁₂.map := by simp [f, h]
  have hf₀₂ (j : Fin (n + 4)) (hj) (h : j.val = n + 2) : f j hj = h₀₂.map := by simp [f, h]
  have hf₀₁ (j : Fin (n + 4)) (hj) (h : j.val = n + 3) : f j hj = h₀₁.map := by simp [f, h]
  have hf (j : Fin (n + 4)) (hj) (h : j.val ≤ n) : f j hj = const e := by
    simp [f, show j.val ≠ n + 1 by omega, show j.val ≠ n + 2 by omega,
      show j.val ≠ n + 3 by omega]
  obtain ⟨Φ, hΦ, hΦp⟩ := (isCompatible_of_δ_succ (f := f) (x := e) fun j hj l ↦ by
    dsimp only [f]
    split_ifs <;> simp).exists_lift p hs.map fun j hj ↦ by
      by_cases h₁ : j.val = n + 1
      · obtain rfl : j = (Fin.last (n + 1)).castSucc.castSucc := Fin.ext (by simpa using h₁)
        rw [hf₁₂ _ hj h₁, h₁₂.map_comp, hs.δ_castSucc_castSucc_map]
      by_cases h₂ : j.val = n + 2
      · obtain rfl : j = (Fin.last (n + 1)).castSucc.succ := Fin.ext (by simpa using h₂)
        rw [hf₀₂ _ hj h₂, h₀₂.map_comp, hs.δ_succ_castSucc_map]
      by_cases h₃ : j.val = n + 3
      · obtain rfl : j = (Fin.last (n + 1)).succ.succ := Fin.ext (by simpa using h₃)
        rw [hf₀₁ _ hj h₃, h₀₁.map_comp, hs.δ_succ_succ_map]
      have h : j.val ≤ n := by omega
      rw [hf j hj h, const_comp, he, hs.δ_map_of_lt j (by simp [Fin.lt_def]; omega)]
  have hj₀ {j : Fin (n + 4)} {m : ℕ} (h : j.val = n + m + 1) : j ≠ 0 := fun h₀ ↦ by
    rw [h₀, Fin.val_zero] at h
    omega
  exact ⟨Φ, hΦp, fun j hj h ↦ by rw [hΦ j hj, hf j hj h],
    fun j h ↦ by rw [hΦ j (hj₀ (m := 0) h), hf₁₂ j (hj₀ (m := 0) h) h],
    fun j h ↦ by rw [hΦ j (hj₀ (m := 1) h), hf₀₂ j (hj₀ (m := 1) h) h],
    fun j h ↦ by rw [hΦ j (hj₀ (m := 2) h), hf₀₁ j (hj₀ (m := 2) h) h]⟩

/-- The connecting map `π (n + 2) B b → π (n + 1) F e` is multiplicative. -/
lemma δ_mul {n : ℕ} (x y : π (n + 2) B b) :
    δ p he (n + 1) (x * y) = δ p he (n + 1) x * δ p he (n + 1) y := by
  induction x with | mk s₀₁
  induction y with | mk s₁₂
  obtain ⟨s₀₂, ⟨hs⟩⟩ := PtSimplex.MulStruct.nonempty s₀₁ s₁₂ (Fin.last _)
  obtain ⟨t₀₁, ⟨h₀₁⟩⟩ := exists_deltaStruct he s₀₁
  obtain ⟨t₁₂, ⟨h₁₂⟩⟩ := exists_deltaStruct he s₁₂
  obtain ⟨t₀₂, ⟨h₀₂⟩⟩ := exists_deltaStruct he s₀₂
  rw [π.mul_mk_eq_iff.2 ⟨hs⟩, δ_mk_eq_of_deltaStruct h₀₁, δ_mk_eq_of_deltaStruct h₁₂,
    δ_mk_eq_of_deltaStruct h₀₂, eq_comm, π.mul_mk_eq_iff]
  -- The face `0` of the lift of the `MulStruct` is a `MulStruct` in the fiber.
  obtain ⟨Φ, hΦp, hΦ, hΦ₁₂, hΦ₀₂, hΦ₀₁⟩ := exists_lift_of_mulStruct hs h₀₁ h₁₂ h₀₂
  have hΦ₀ : (stdSimplex.δ 0 ≫ Φ) ≫ p = const b := by
    rw [Category.assoc, hΦp, hs.δ_map_of_lt 0 (by simp [Fin.lt_def])]
  have hface (j : Fin (n + 3)) :
      stdSimplex.δ j ≫ fiber.lift (stdSimplex.δ 0 ≫ Φ) p b hΦ₀ ≫ (fiber p b).ι =
        stdSimplex.δ 0 ≫ stdSimplex.δ j.succ ≫ Φ := by
    rw [fiber.lift_ι, δ_comp_δ_zero_assoc]
  exact ⟨{
    map := fiber.lift (stdSimplex.δ 0 ≫ Φ) p b hΦ₀
    δ_castSucc_castSucc_map := by
      rw [← cancel_mono (fiber p b).ι, Category.assoc, hface, hΦ₁₂ _ (by simp)]
      exact h₁₂.δ_zero_map
    δ_succ_castSucc_map := by
      rw [← cancel_mono (fiber p b).ι, Category.assoc, hface, hΦ₀₂ _ (by simp)]
      exact h₀₂.δ_zero_map
    δ_succ_succ_map := by
      rw [← cancel_mono (fiber p b).ι, Category.assoc, hface, hΦ₀₁ _ (by simp)]
      exact h₀₁.δ_zero_map
    δ_map_of_lt := fun j hj ↦ by
      rw [← cancel_mono (fiber p b).ι, Category.assoc, hface,
        hΦ _ (Fin.succ_ne_zero _) (by rw [Fin.val_succ]; simp [Fin.lt_def] at hj; omega)]
      simp
    δ_map_of_gt := fun j hj ↦ absurd hj (not_lt.2 (by simpa using Fin.le_last j)) }⟩

variable (p he) in
/-- The connecting map `π (n + 2) B b →* π (n + 1) F e`, as a group homomorphism. -/
noncomputable def δHom (n : ℕ) :
    π (n + 2) B b →* π (n + 1) (fiber p b : SSet) (fiber.basePoint p he) :=
  MonoidHom.mk' (δ p he (n + 1)) δ_mul

@[simp]
lemma δHom_apply {n : ℕ} (x : π (n + 2) B b) : δHom p he n x = δ p he (n + 1) x :=
  (rfl)

end HomotopySequence

end KanComplex

end SSet
