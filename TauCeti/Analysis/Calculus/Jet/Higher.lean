/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Symmetric
public import TauCeti.Analysis.Calculus.Jet.Equivalence
public import TauCeti.Analysis.Calculus.Jet.HigherOrder
public import TauCeti.Analysis.Calculus.Jet.Realization
public import TauCeti.Analysis.Calculus.Jet.Section

/-!
# Finite jets of local sections in a bundle chart

`TauCeti.JetAt 𝕜 F r x` is the set of jets of order `r` at `x` of local sections with fibre `F`:
maps smooth near `x`, identified when they have the same value and the same derivatives through
order `r` at `x` (`TauCeti.SameJetAt`). Representatives need only be smooth near `x`, so a section
defined on a chart domain is used through an arbitrary extension.

The coordinates of a jet are its derivative tuple `(f x, Df(x), …, Dʳf(x))`, indexed by
`Fin (r + 1)`, and they determine the jet. A jet of order `r` truncates to a jet of every lower
order; truncations compose, and order-zero jets are field values. A base change `h` together
with a base-dependent, possibly nonlinear, fibre change `g` maps the jet of `s` to the jet of
`y ↦ g (y, s (h y))`. These maps satisfy the identity, composition and inverse laws and commute
with truncation, which is the chart independence of the jet bundle at the level of a single
fibre. On coordinates they act by the higher-order chain rule `TauCeti.jetCoordChange`.

Over `ℝ` or `ℂ` the derivative tuple of a jet consists of symmetric multilinear maps, and every
symmetric tuple is the derivative tuple of exactly one jet, realized by its Taylor polynomial
(`TauCeti.finiteJetPolynomial`). Thus `JetAt.coordinatesEquiv` identifies the jets in a chart with
symmetric tuples, the fibre coordinates of the jet bundle, and every jet is realized by a
globally smooth section whose graph stays in any prescribed neighborhood
(`JetAt.exists_section_eventually_mem`). The coordinate identification depends
on the chart; no vector-space structure is selected on the quotient itself. For order one the
quotient is `TauCeti.FirstJetAt`, with its explicit first-order transformation law.

## Main definitions and results

* `TauCeti.JetAt`: jets of order `r` at a point of local sections smooth near that point.
* `TauCeti.JetAt.mk_eq_mk_iff`: two sections define the same jet exactly when they have the same
  jet in the sense of `TauCeti.SameJetAt`.
* `TauCeti.JetAt.truncate`: truncation to lower order, with `JetAt.truncate_truncate`.
* `TauCeti.JetAt.map`: the transformation of jets by a nonlinear change of bundle coordinates,
  with `JetAt.map_mk`, `JetAt.coordinates_map`, `JetAt.map_congr`, `JetAt.map_id`,
  `JetAt.map_comp`, `JetAt.coordinates_map_inverse` and `JetAt.truncate_map`.
* `TauCeti.JetAt.coordinatesEquiv`: over `ℝ` or `ℂ`, jets correspond to symmetric derivative
  tuples.
* `TauCeti.JetAt.zeroEquiv` and `TauCeti.JetAt.firstJetAtEquiv`: jets of order zero are values,
  and jets of order one are first jets, with the same transformation law
  (`JetAt.firstJetAtEquiv_map`).

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A.
* Kolář, Michor and Slovák, *Natural Operations in Differential Geometry*, Chapter 12.
-/

public section

noncomputable section

open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 E E' E'' F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Jets of order `r` at `x` of local smooth sections in a bundle chart with fibre `F`.
Only the germ near `x` must be smooth. Two sections are identified when their values and
derivatives through order `r` agree at `x`. -/
def JetAt (𝕜 : Type*) {E : Type*} (F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (r : ℕ) (x : E) :=
  Quotient ((SameJetAt.setoid 𝕜 F r x).comap
    (Subtype.val : {s : E → F // ContDiffAt 𝕜 ∞ s x} → E → F))

namespace JetAt

variable {r m : ℕ}

/-- The relation defining jets is equality of finite jets of the representatives. -/
private theorem rel_iff {x : E} {s t : {s : E → F // ContDiffAt 𝕜 ∞ s x}} :
    (SameJetAt.setoid 𝕜 F r x).comap Subtype.val s t ↔ SameJetAt 𝕜 r x s.val t.val := by
  rw [Setoid.comap_rel, SameJetAt.setoid_apply]

/-- The jet of order `r` of a section smooth near `x`. -/
def mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) : JetAt 𝕜 F r x :=
  Quotient.mk'' ⟨s, hs⟩

/-- Two local sections define the same jet exactly when they have equal finite jets. -/
@[simp]
theorem mk_eq_mk_iff {x : E} {s t : E → F} (hs : ContDiffAt 𝕜 ∞ s x)
    (ht : ContDiffAt 𝕜 ∞ t x) :
    (mk s hs : JetAt 𝕜 F r x) = mk t ht ↔ SameJetAt 𝕜 r x s t :=
  Quotient.eq''.trans rel_iff

/-- Every jet is the jet of a local section. -/
@[elab_as_elim]
theorem ind {x : E} {motive : JetAt 𝕜 F r x → Prop}
    (h : ∀ s (hs : ContDiffAt 𝕜 ∞ s x), motive (mk s hs)) (j : JetAt 𝕜 F r x) : motive j :=
  Quotient.ind (fun s ↦ h s.val s.property) j

/-- Every jet has a representative section, as an existence statement. -/
theorem mk_surjective {x : E} (j : JetAt 𝕜 F r x) :
    ∃ (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x), mk s hs = j := by
  induction j using ind with | h s hs => exact ⟨s, hs, rfl⟩

/-- The quotient forgets how a local section is extended away from the point. -/
theorem mk_eq_mk_of_eventuallyEq {x : E} {s t : E → F}
    (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x) (h : s =ᶠ[𝓝 x] t) :
    (mk s hs : JetAt 𝕜 F r x) = mk t ht :=
  (mk_eq_mk_iff hs ht).2 h.sameJetAt

/-- Universal property of jets: a function of local sections smooth near `x` which depends only
on their jets of order `r` descends to `JetAt 𝕜 F r x`. -/
def lift {α : Sort*} {x : E} (f : ∀ s : E → F, ContDiffAt 𝕜 ∞ s x → α)
    (hf : ∀ (s t : E → F) (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x),
      SameJetAt 𝕜 r x s t → f s hs = f t ht) :
    JetAt 𝕜 F r x → α :=
  Quotient.lift (fun s ↦ f s.val s.property) fun s t h ↦ hf s.val t.val s.property t.property
      (rel_iff.1 h)

@[simp]
theorem lift_mk {α : Sort*} {x : E} (f : ∀ s : E → F, ContDiffAt 𝕜 ∞ s x → α)
    (hf : ∀ (s t : E → F) (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x),
      SameJetAt 𝕜 r x s t → f s hs = f t ht)
    (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    lift f hf (mk s hs) = f s hs :=
  (rfl)

/-- The derivative tuple `(s x, Ds(x), …, Dʳs(x))` of a jet in the selected chart. -/
def coordinates {x : E} : JetAt 𝕜 F r x → (i : Fin (r + 1)) → E [×i]→L[𝕜] F :=
  Quotient.lift (fun s ↦ fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i s.val x)
    fun _ _ h ↦ funext fun i ↦ (rel_iff.mp h).iteratedFDeriv_eq (Nat.lt_succ_iff.mp i.isLt)

@[simp]
theorem coordinates_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) (i : Fin (r + 1)) :
    coordinates (mk s hs : JetAt 𝕜 F r x) i = iteratedFDeriv 𝕜 i s x :=
  (rfl)

/-- A jet is determined by its derivative tuple. -/
theorem coordinates_injective {x : E} :
    Function.Injective (coordinates : JetAt 𝕜 F r x → _) := by
  intro j k hjk
  induction j using ind with | h s hs =>
  induction k using ind with | h t ht =>
  refine (mk_eq_mk_iff hs ht).2 (sameJetAt_iff.2 fun i hi ↦ ?_)
  simpa using congrFun hjk ⟨i, Nat.lt_succ_of_le hi⟩

@[ext]
theorem ext {x : E} {j k : JetAt 𝕜 F r x} (h : ∀ i, coordinates j i = coordinates k i) :
    j = k :=
  coordinates_injective (funext h)

/-- The value of a jet, which is its order-zero coordinate. -/
def value {x : E} (j : JetAt 𝕜 F r x) : F :=
  coordinates j 0 0

@[simp]
theorem value_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    value (mk s hs : JetAt 𝕜 F r x) = s x :=
  iteratedFDeriv_zero_apply _

/-- The order-zero coordinate of a jet is its value. -/
theorem coordinates_zero_apply {x : E} (j : JetAt 𝕜 F r x) (v : Fin 0 → E) :
    coordinates j 0 v = value j := by
  induction j using ind with | h s hs =>
  rw [value_mk, coordinates_mk]
  exact iteratedFDeriv_zero_apply v

/-- Every value is the value of a jet, for instance of a constant section. -/
theorem value_surjective (x : E) :
    Function.Surjective (value : JetAt 𝕜 F r x → F) :=
  fun v ↦ ⟨mk (fun _ ↦ v) contDiffAt_const, value_mk _ _⟩

/-! ### Truncation -/

/-- Truncation of a jet of order `r` to a jet of lower order `m`. -/
def truncate {x : E} (hmr : m ≤ r) : JetAt 𝕜 F r x → JetAt 𝕜 F m x :=
  Quotient.map' id fun _ _ h ↦ rel_iff.2 ((rel_iff.1 h).of_le hmr)

@[simp]
theorem truncate_mk {x : E} (hmr : m ≤ r) (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    truncate hmr (mk s hs : JetAt 𝕜 F r x) = mk s hs :=
  (rfl)

/-- The coordinates of a truncation are the lower-order coordinates. -/
@[simp]
theorem coordinates_truncate {x : E} (hmr : m ≤ r) (j : JetAt 𝕜 F r x) (i : Fin (m + 1)) :
    coordinates (truncate hmr j) i = coordinates j (Fin.castLE (Nat.succ_le_succ hmr) i) := by
  induction j using ind with | h s hs => simp

@[simp]
theorem value_truncate {x : E} (hmr : m ≤ r) (j : JetAt 𝕜 F r x) :
    value (truncate hmr j) = value j := by
  induction j using ind with | h s hs => simp

/-- Truncating to the same order is the identity. -/
@[simp]
theorem truncate_self {x : E} (j : JetAt 𝕜 F r x) : truncate le_rfl j = j := by
  induction j using ind with | h s hs => simp

/-- Truncations compose. -/
@[simp]
theorem truncate_truncate {x : E} {l : ℕ} (hlm : l ≤ m) (hmr : m ≤ r)
    (j : JetAt 𝕜 F r x) : truncate hlm (truncate hmr j) = truncate (hlm.trans hmr) j := by
  induction j using ind with | h s hs => simp

/-- Truncation is surjective: every lower-order jet extends to a jet of higher order. -/
theorem truncate_surjective {x : E} (hmr : m ≤ r) :
    Function.Surjective (truncate hmr : JetAt 𝕜 F r x → JetAt 𝕜 F m x) := by
  intro j
  induction j using ind with | h s hs => exact ⟨mk s hs, rfl⟩

/-- Jets of order zero are field values. -/
def zeroEquiv (x : E) : JetAt 𝕜 F 0 x ≃ F where
  toFun := value
  invFun v := mk (fun _ ↦ v) contDiffAt_const
  left_inv j := by
    induction j using ind with | h s hs =>
    simp [mk_eq_mk_iff, sameJetAt_zero_iff]
  right_inv v := value_mk _ _

@[simp]
theorem zeroEquiv_apply {x : E} (j : JetAt 𝕜 F 0 x) : zeroEquiv x j = value j :=
  (rfl)

@[simp]
theorem zeroEquiv_symm_apply {x : E} (v : F) :
    (zeroEquiv x).symm v = (mk (fun _ ↦ v) contDiffAt_const : JetAt 𝕜 F 0 x) :=
  (rfl)

/-- Jets of order one are the first jets of `TauCeti.FirstJetAt`, which have an explicit
first-order transformation law. -/
def firstJetAtEquiv (x : E) : JetAt 𝕜 F 1 x ≃ FirstJetAt 𝕜 F x where
  toFun := Quotient.lift (fun s ↦ FirstJetAt.mk s.val s.property) fun _ _ h ↦
    (FirstJetAt.mk_eq_mk_iff _ _).2 (sameJetAt_one_iff.1 (rel_iff.1 h))
  invFun j := mk (FirstJetAt.exists_section j).choose
    (FirstJetAt.exists_section j).choose_spec.choose.contDiffAt
  left_inv j := by
    induction j using ind with | h s hs =>
    rw [mk_eq_mk_iff, sameJetAt_one_iff, ← FirstJetAt.mk_eq_mk_iff _ hs]
    exact (FirstJetAt.exists_section _).choose_spec.choose_spec
  right_inv j := (FirstJetAt.exists_section j).choose_spec.choose_spec

@[simp]
theorem firstJetAtEquiv_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    firstJetAtEquiv x (mk s hs) = FirstJetAt.mk s hs :=
  (rfl)

@[simp]
theorem firstJetAtEquiv_symm_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    (firstJetAtEquiv x).symm (FirstJetAt.mk s hs) = mk s hs :=
  (Equiv.symm_apply_eq _).2 rfl

@[simp]
theorem value_firstJetAtEquiv {x : E} (j : JetAt 𝕜 F 1 x) :
    FirstJetAt.value (firstJetAtEquiv x j) = value j := by
  induction j using ind with | h s hs => simp

/-- The first-jet coordinates of an order-one jet are its value and its first coordinate, read
as a continuous linear map. -/
@[simp]
theorem coordinates_firstJetAtEquiv {x : E} (j : JetAt 𝕜 F 1 x) :
    FirstJetAt.coordinates (firstJetAtEquiv x j) =
      (value j, continuousMultilinearCurryFin1 𝕜 E F (coordinates j 1)) := by
  induction j using ind with | h s hs =>
  ext v <;> simp [iteratedFDeriv_one_apply]

@[simp]
theorem value_firstJetAtEquiv_symm {x : E} (j : FirstJetAt 𝕜 F x) :
    value ((firstJetAtEquiv x).symm j) = FirstJetAt.value j := by
  obtain ⟨_, _, rfl⟩ := FirstJetAt.exists_section j
  simp

/-- The first coordinate of the order-one jet of a first jet is its derivative, read as a
multilinear map. -/
@[simp]
theorem coordinates_firstJetAtEquiv_symm_one {x : E} (j : FirstJetAt 𝕜 F x) :
    coordinates ((firstJetAtEquiv x).symm j) 1 =
      (continuousMultilinearCurryFin1 𝕜 E F).symm (FirstJetAt.coordinates j).2 := by
  obtain ⟨s, hs, rfl⟩ := FirstJetAt.exists_section j
  ext v
  simp [iteratedFDeriv_one_apply]

/-! ### Changes of bundle coordinates -/

/-- A chosen representative of a jet, used to transform jets. -/
private def rep {x : E} (j : JetAt 𝕜 F r x) : E → F :=
  (Quotient.out j).val

private theorem contDiffAt_rep {x : E} (j : JetAt 𝕜 F r x) : ContDiffAt 𝕜 ∞ (rep j) x :=
  (Quotient.out j).property

private theorem mk_rep {x : E} (j : JetAt 𝕜 F r x) : mk (rep j) (contDiffAt_rep j) = j :=
  Quotient.out_eq j

private theorem rep_apply {x : E} (j : JetAt 𝕜 F r x) : rep j x = value j := by
  conv_rhs => rw [← mk_rep j]
  rw [value_mk]

open Classical in
/-- Transform the jet of `s` at `h x` into the jet of `y ↦ g (y, s (h y))` at `x`, for a base
change `h` and a base-dependent, possibly nonlinear, fibre change `g`. This is well defined
when `h` is smooth at `x` and `g` is smooth at `(x, value j)`, by `JetAt.map_mk`; otherwise it
is the jet of a constant section with the transformed value. -/
def map {x : E'} (h : E' → E) (g : E' × F → G) (j : JetAt 𝕜 F r (h x)) : JetAt 𝕜 G r x :=
  if hc : ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, value j) then
    mk (fun y ↦ g (y, rep j (h y))) ((rep_apply j ▸ hc.2).comp x
      (contDiffAt_id.prodMk ((contDiffAt_rep j).comp x hc.1)))
  else mk (fun _ ↦ g (x, value j)) contDiffAt_const

/-- Transforming the jet of a section is the jet of the transformed section. In particular the
transformed jet depends only on the input jet. -/
@[simp]
theorem map_mk {x : E'} (h : E' → E) (g : E' × F → G) (s : E → F)
    (hs : ContDiffAt 𝕜 ∞ s (h x)) (hh : ContDiffAt 𝕜 ∞ h x)
    (hg : ContDiffAt 𝕜 ∞ g (x, s (h x))) :
    map h g (mk s hs : JetAt 𝕜 F r (h x)) =
      mk (fun y ↦ g (y, s (h y))) (hg.comp x (contDiffAt_id.prodMk (hs.comp x hh))) := by
  have hc : ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, value (mk s hs : JetAt 𝕜 F r (h x))) :=
    ⟨hh, by simpa using hg⟩
  rw [map, dite_eq_left hc, mk_eq_mk_iff]
  have hrep := mk_rep (mk s hs : JetAt 𝕜 F r (h x))
  rw [mk_eq_mk_iff] at hrep
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  exact hrep.coordChange ((contDiffAt_rep _).of_le hr) (hs.of_le hr) (hh.of_le hr)
    ((by simpa only [hrep.apply_eq] using hg : ContDiffAt 𝕜 ∞ g _).of_le hr)

/-- For smooth changes of bundle coordinates, a transformed jet has the coordinates given by the
higher-order chain rule `TauCeti.jetCoordChange`. -/
@[simp]
theorem coordinates_map {x : E'} (h : E' → E) (g : E' × F → G) (j : JetAt 𝕜 F r (h x))
    (hh : ContDiffAt 𝕜 ∞ h x) (hg : ContDiffAt 𝕜 ∞ g (x, value j)) :
    coordinates (map h g j) = jetCoordChange r h g x (coordinates j) := by
  induction j using ind with | h s hs =>
  rw [value_mk] at hg
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [map_mk h g s hs hh hg]
  exact (jetCoordChange_iteratedFDeriv (hh.of_le hr) (hs.of_le hr) (hg.of_le hr)).symm

/-- The value of a transformed jet is the transformed value. -/
@[simp]
theorem value_map {x : E'} (h : E' → E) (g : E' × F → G) (j : JetAt 𝕜 F r (h x)) :
    value (map h g j) = g (x, value j) := by
  rw [map]
  split_ifs with hc
  · rw [value_mk, rep_apply]
  · exact value_mk _ _

/-- Transforming jets depends only on the germs of the changes of bundle coordinates and on the
coordinates of the jet. -/
theorem map_congr {x : E'} {h h' : E' → E} {g g' : E' × F → G} {j : JetAt 𝕜 F r (h x)}
    {j' : JetAt 𝕜 F r (h' x)} (hh : h =ᶠ[𝓝 x] h') (hg : g =ᶠ[𝓝 (x, value j)] g')
    (hj : coordinates j = coordinates j') :
    map h g j = map h' g' j' := by
  have hv : value j = value j' := by rw [value, value, hj]
  have hc_iff : (ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, value j)) ↔
      (ContDiffAt 𝕜 ∞ h' x ∧ ContDiffAt 𝕜 ∞ g' (x, value j')) := by
    rw [← hv]
    exact and_congr
      ⟨fun h₁ ↦ h₁.congr_of_eventuallyEq hh.symm, fun h₁ ↦ h₁.congr_of_eventuallyEq hh⟩
      ⟨fun h₁ ↦ h₁.congr_of_eventuallyEq hg.symm, fun h₁ ↦ h₁.congr_of_eventuallyEq hg⟩
  by_cases hc : ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, value j)
  · have hc' := hc_iff.mp hc
    refine coordinates_injective ?_
    rw [coordinates_map h g j hc.1 hc.2, coordinates_map h' g' j' hc'.1 hc'.2, ← hj]
    exact jetCoordChange_congr (coordinates j) hh hg
  · rw [map, dite_eq_right hc, map, dite_eq_right (mt hc_iff.mpr hc)]
    simp only [← hv, hg.eq_of_nhds]

/-- Identity coordinate changes induce the identity on jets. -/
@[simp]
theorem map_id {x : E} (j : JetAt 𝕜 F r x) : map id Prod.snd j = j := by
  induction j using ind with | h s hs =>
  exact map_mk id Prod.snd s hs contDiffAt_id contDiffAt_snd

/-- The composite of two changes of bundle coordinates is smooth. -/
private theorem contDiffAt_fibreComp {y : E''} {v : F} {k : E'' → E'} {g : E' × F → G}
    {l : E'' × G → H} (hk : ContDiffAt 𝕜 ∞ k y) (hg : ContDiffAt 𝕜 ∞ g (k y, v))
    (hl : ContDiffAt 𝕜 ∞ l (y, g (k y, v))) :
    ContDiffAt 𝕜 ∞ (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) (y, v) :=
  hl.comp (y, v) (contDiffAt_fst.prodMk
    (hg.comp (y, v) ((hk.comp _ contDiffAt_fst).prodMk contDiffAt_snd)))

/-- Nonlinear changes of bundle coordinates compose on jets of every order. -/
theorem map_comp {y : E''} (h : E' → E) (k : E'' → E') (g : E' × F → G) (l : E'' × G → H)
    (j : JetAt 𝕜 F r (h (k y))) (hh : ContDiffAt 𝕜 ∞ h (k y)) (hk : ContDiffAt 𝕜 ∞ k y)
    (hg : ContDiffAt 𝕜 ∞ g (k y, value j)) (hl : ContDiffAt 𝕜 ∞ l (y, g (k y, value j))) :
    map k l (map h g j) = map (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) j := by
  induction j using ind with | h s hs =>
  simp only [value_mk] at hg hl
  rw [map_mk h g s hs hh hg, map_mk k l _ _ hk hl,
    map_mk (h ∘ k) _ s hs (hh.comp y hk) (contDiffAt_fibreComp hk hg hl)]
  rfl

/-- Changes of bundle coordinates which are inverse as germs restore the jet coordinates. The
base points agree by the base germ identity; the coordinate statement avoids transport between
the dependent quotient types at those equal points. -/
theorem coordinates_map_inverse {x : E} (h : E' → E) (k : E → E') (g : E' × F → G)
    (l : E × G → F) (j : JetAt 𝕜 F r (h (k x))) (hh : ContDiffAt 𝕜 ∞ h (k x))
    (hk : ContDiffAt 𝕜 ∞ k x) (hg : ContDiffAt 𝕜 ∞ g (k x, value j))
    (hl : ContDiffAt 𝕜 ∞ l (x, g (k x, value j))) (hbase : h ∘ k =ᶠ[𝓝 x] id)
    (hfibre : (fun p : E × F ↦ l (p.1, g (k p.1, p.2))) =ᶠ[𝓝 (x, value j)] Prod.snd) :
    coordinates (map k l (map h g j)) = coordinates j := by
  rw [map_comp h k g l j hh hk hg hl]
  induction j using ind with | h s hs =>
  simp only [value_mk] at hg hl hfibre
  have hx : h (k x) = x := hbase.eq_of_nhds
  rw [map_mk (h ∘ k) _ s hs (hh.comp x hk) (contDiffAt_fibreComp hk hg hl)]
  -- Near `x` the transformed section is `s` itself.
  have heq : (fun y ↦ l (y, g (k y, s (h (k y))))) =ᶠ[𝓝 x] s :=
    eventuallyEq_of_inverse_germ hbase (by simpa only [hx] using hs.continuousAt)
      (by simpa only [hx] using hfibre)
  funext i
  simp only [coordinates_mk, Function.comp_apply, hx]
  exact (heq.iteratedFDeriv 𝕜 i).eq_of_nhds

/-- Changes of bundle coordinates commute with truncation. -/
@[simp]
theorem truncate_map {x : E'} (hmr : m ≤ r) (h : E' → E) (g : E' × F → G)
    (j : JetAt 𝕜 F r (h x)) : truncate hmr (map h g j) = map h g (truncate hmr j) := by
  induction j using ind with | h s hs =>
  by_cases hc : ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, s (h x))
  · rw [map_mk h g s hs hc.1 hc.2, truncate_mk, truncate_mk, map_mk h g s hs hc.1 hc.2]
  · have hc' (n : ℕ) :
        ¬(ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, value (mk s hs : JetAt 𝕜 F n (h x)))) := by
      simpa using hc
    rw [map, dite_eq_right (hc' r), map, dite_eq_right (by simpa using hc' m)]
    simp

/-- For smooth changes of bundle coordinates, the order-one jet map is the first-jet map
`TauCeti.FirstJetAt.map`, with its explicit transformation law `FirstJetAt.coordinates_map`. -/
theorem firstJetAtEquiv_map {x : E'} (h : E' → E) (g : E' × F → G) (j : JetAt 𝕜 F 1 (h x))
    (hh : ContDiffAt 𝕜 ∞ h x) (hg : ContDiffAt 𝕜 ∞ g (x, value j)) :
    firstJetAtEquiv x (map h g j) = FirstJetAt.map h g (firstJetAtEquiv (h x) j) := by
  induction j using ind with | h s hs =>
  rw [value_mk] at hg
  rw [map_mk h g s hs hh hg, firstJetAtEquiv_mk, firstJetAtEquiv_mk,
    FirstJetAt.map_mk h g s hs hh hg]

/-! ### Symmetric coordinates -/

/-- Over `ℝ` or `ℂ`, the coordinates of a jet are symmetric multilinear maps. -/
theorem coordinates_comp_perm [IsRCLikeNormedField 𝕜] {x : E} (j : JetAt 𝕜 F r x)
    (i : Fin (r + 1)) (v : Fin i → E) (σ : Equiv.Perm (Fin i)) :
    coordinates j i (v ∘ σ) = coordinates j i v := by
  induction j using ind with | h s hs =>
  simp only [coordinates_mk]
  exact hs.iteratedFDeriv_comp_perm_of_minSmoothness_le (by simp) v σ

/-- In characteristic zero every symmetric tuple is the derivative tuple of the jet of its
Taylor polynomial. -/
@[simp]
theorem coordinates_mk_finiteJetPolynomial [CharZero 𝕜] {x : E}
    (A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F)
    (hA : ∀ (i : Fin (r + 1)) (v : Fin i → E) (σ : Equiv.Perm (Fin i)), A i (v ∘ σ) = A i v) :
    coordinates (mk (finiteJetPolynomial r A x)
      (contDiff_finiteJetPolynomial r A x).contDiffAt : JetAt 𝕜 F r x) = A := by
  funext i
  exact iteratedFDeriv_finiteJetPolynomial_self r A x i (hA i)

/-- Over `ℝ` or `ℂ`, the coordinates identify the jets in a chart with the tuples of symmetric
multilinear maps (`TauCeti.symmetricJets`), the fibre coordinates of the jet bundle. The inverse
sends a tuple to the jet of its Taylor polynomial. -/
def coordinatesEquiv [IsRCLikeNormedField 𝕜] (r : ℕ) (x : E) :
    JetAt 𝕜 F r x ≃ symmetricJets 𝕜 E F r :=
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  { toFun j := ⟨coordinates j, mem_symmetricJets.2 (coordinates_comp_perm j)⟩
    invFun A := mk (finiteJetPolynomial r A.val x) (contDiff_finiteJetPolynomial r A.val
        x).contDiffAt
    left_inv j := coordinates_injective
      (coordinates_mk_finiteJetPolynomial _ (coordinates_comp_perm j))
    right_inv A :=
      Subtype.ext (coordinates_mk_finiteJetPolynomial A.val (mem_symmetricJets.1 A.property)) }

@[simp]
theorem coordinatesEquiv_symm_apply [IsRCLikeNormedField 𝕜] {x : E}
    (A : symmetricJets 𝕜 E F r) :
    (coordinatesEquiv r x).symm A =
      mk (finiteJetPolynomial r A.val x) (contDiff_finiteJetPolynomial r A.val x).contDiffAt :=
  (rfl)

@[simp]
theorem coe_coordinatesEquiv [IsRCLikeNormedField 𝕜] {x : E} (j : JetAt 𝕜 F r x) :
    (coordinatesEquiv r x j : (i : Fin (r + 1)) → E [×i]→L[𝕜] F) = coordinates j :=
  (rfl)

/-- Every jet over `ℝ` or `ℂ` is the jet of the Taylor polynomial of its coordinates, an
analytic section defined on the whole chart. -/
theorem mk_finiteJetPolynomial_coordinates [IsRCLikeNormedField 𝕜] {x : E}
    (j : JetAt 𝕜 F r x) :
    mk (finiteJetPolynomial r (coordinates j) x)
      (contDiff_finiteJetPolynomial r (coordinates j) x).contDiffAt = j :=
  (coordinatesEquiv r x).left_inv j

theorem coordinates_coordinatesEquiv_symm [IsRCLikeNormedField 𝕜] {x : E}
    (A : symmetricJets 𝕜 E F r) :
    coordinates ((coordinatesEquiv r x).symm A) = A.val :=
  congrArg Subtype.val ((coordinatesEquiv r x).apply_symm_apply A)

theorem value_coordinatesEquiv_symm [IsRCLikeNormedField 𝕜] {x : E}
    (A : symmetricJets 𝕜 E F r) :
    value ((coordinatesEquiv r x).symm A) = A.val 0 0 := by
  rw [value, coordinates_coordinatesEquiv_symm]

/-- Over `ℝ` or `ℂ`, every jet is the jet of a globally smooth section whose graph stays near `x`
in any prescribed neighborhood of `(x, value j)`. -/
theorem exists_section_eventually_mem [IsRCLikeNormedField 𝕜] {x : E} (j : JetAt 𝕜 F r x)
    {u : Set (E × F)} (hu : u ∈ 𝓝 (x, value j)) :
    ∃ (s : E → F) (hs : ContDiff 𝕜 ∞ s), mk s hs.contDiffAt = j ∧ ∀ᶠ y in 𝓝 x, (y, s y) ∈ u := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  obtain ⟨s, hs, hsj, hsu⟩ := exists_contDiff_iteratedFDeriv_eq_eventually_mem r (coordinates j)
    (coordinates_comp_perm j) x hu
  exact ⟨s, hs.of_le (by simp), coordinates_injective (funext hsj), hsu⟩

/-- Over `ℝ` or `ℂ`, every jet is the jet of a globally smooth section. -/
theorem exists_section [IsRCLikeNormedField 𝕜] {x : E} (j : JetAt 𝕜 F r x) :
    ∃ (s : E → F) (hs : ContDiff 𝕜 ∞ s), mk s hs.contDiffAt = j :=
  let ⟨s, hs, hsj, _⟩ := exists_section_eventually_mem j Filter.univ_mem
  ⟨s, hs, hsj⟩

end JetAt

end TauCeti
