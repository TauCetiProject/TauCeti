/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
public import TauCeti.Analysis.Calculus.Jet.Section

/-!
# Jets of arbitrary finite order of local sections in a bundle chart

`TauCeti.JetAt 𝕜 F r x` is the quotient of maps smooth near `x` by equality of their iterated
derivatives of every order `k ≤ r` at `x`. Over `ℝ` or `ℂ` the iterated derivatives of smooth
maps are symmetric, so these are the symmetric derivative coordinates `u^a_I`, `|I| ≤ r`, of a jet
in the chosen chart. Representatives need only be smooth near `x`, so the carrier applies to
sections defined on chart domains.

The main result is that this equivalence relation does not depend on bundle coordinates: a base
change `h` together with a base-dependent nonlinear fibre map `g` transforms jets of sections,
`JetAt.map`, and the transformed jet depends only on the original jet (`JetAt.map_mk`). This is
the locality of the Faà di Bruno formula, `iteratedFDeriv_comp_congr`. The induced maps satisfy
the identity, composition and local inverse laws, and commute with the truncations
`JetAt.truncate` to lower order. Order zero recovers the field value (`JetAt.zeroEquiv`), and
order one recovers `TauCeti.FirstJetAt` compatibly with coordinate changes
(`JetAt.firstJetAtEquiv`, `JetAt.firstJetAtEquiv_map`).

No vector-space structure is selected on these quotients, and no global jet bundle is built here.

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
Only the germ near `x` must be smooth. The equivalence relation identifies sections whose
iterated derivatives at `x` agree in every order `k ≤ r`. -/
def JetAt (𝕜 : Type*) {E : Type*} (F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (r : ℕ) (x : E) :=
  Quotient (Setoid.ker (fun s : {s : E → F // ContDiffAt 𝕜 ∞ s x} ↦
    fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k s.1 x))

namespace JetAt

variable {r : ℕ}

/-- The jet of order `r` of a section smooth near `x`. -/
def mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) : JetAt 𝕜 F r x :=
  Quotient.mk'' ⟨s, hs⟩

/-- The derivative coordinates of orders `0, …, r` of a jet in the selected bundle chart. -/
def coordinates {x : E} : JetAt 𝕜 F r x → (k : Fin (r + 1)) → E [×k]→L[𝕜] F :=
  Setoid.kerLift _

@[simp]
theorem coordinates_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) (k : Fin (r + 1)) :
    coordinates (mk s hs : JetAt 𝕜 F r x) k = iteratedFDeriv 𝕜 k s x :=
  (rfl)

/-- A jet is determined by its derivative coordinates. -/
@[ext]
theorem ext {x : E} {j k : JetAt 𝕜 F r x} (h : coordinates j = coordinates k) : j = k :=
  Setoid.kerLift_injective _ h

/-- Two local sections define the same jet of order `r` exactly when their iterated derivatives of
every order `k ≤ r` agree. -/
@[simp]
theorem mk_eq_mk_iff {x : E} {s t : E → F} (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x) :
    (mk s hs : JetAt 𝕜 F r x) = mk t ht ↔
      ∀ k ≤ r, iteratedFDeriv 𝕜 k s x = iteratedFDeriv 𝕜 k t x := by
  refine ⟨fun h k hk ↦ congrFun (congrArg coordinates h) ⟨k, Nat.lt_succ_of_le hk⟩,
    fun h ↦ ext (funext fun k ↦ h k (Nat.le_of_lt_succ k.2))⟩

/-- The quotient forgets how a local section is extended away from the point. -/
theorem mk_eq_mk_of_eventuallyEq {x : E} {s t : E → F}
    (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x) (h : s =ᶠ[𝓝 x] t) :
    (mk s hs : JetAt 𝕜 F r x) = mk t ht :=
  (mk_eq_mk_iff hs ht).2 fun k _ ↦ (h.iteratedFDeriv 𝕜 k).eq_of_nhds

/-- Every jet is the jet of some section smooth near the base point. -/
theorem exists_section {x : E} (j : JetAt 𝕜 F r x) :
    ∃ s : E → F, ∃ hs : ContDiffAt 𝕜 ∞ s x, mk s hs = j :=
  Quotient.inductionOn' j fun s ↦ ⟨s.1, s.2, rfl⟩

/-- Order-zero truncation of a jet: the field value, in the selected fibre coordinates. -/
def value {x : E} (j : JetAt 𝕜 F r x) : F :=
  continuousMultilinearCurryFin0 𝕜 E F (coordinates j 0)

@[simp]
theorem value_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    value (mk s hs : JetAt 𝕜 F r x) = s x :=
  (rfl)

/-- The zeroth derivative coordinate of a jet is its value. -/
theorem coordinates_zero {x : E} (j : JetAt 𝕜 F r x) :
    coordinates j 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (value j) :=
  ((continuousMultilinearCurryFin0 𝕜 E F).symm_apply_apply _).symm

/-- Order-zero truncation is surjective, including for zero-dimensional fibres. -/
theorem value_surjective (x : E) : Function.Surjective (value : JetAt 𝕜 F r x → F) :=
  fun v ↦ ⟨mk (fun _ ↦ v) contDiffAt_const, rfl⟩

/-- Truncation of a jet of order `r` to a jet of order `k ≤ r`. -/
def truncate {k : ℕ} (hkr : k ≤ r) {x : E} : JetAt 𝕜 F r x → JetAt 𝕜 F k x :=
  Quotient.map' id fun _ _ h ↦ funext fun i ↦
    congrFun h (Fin.castLE (Nat.succ_le_succ hkr) i)

@[simp]
theorem truncate_mk {k : ℕ} (hkr : k ≤ r) {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    truncate hkr (mk s hs : JetAt 𝕜 F r x) = mk s hs :=
  (rfl)

@[simp]
theorem coordinates_truncate {k : ℕ} (hkr : k ≤ r) {x : E} (j : JetAt 𝕜 F r x)
    (i : Fin (k + 1)) :
    coordinates (truncate hkr j) i = coordinates j (Fin.castLE (Nat.succ_le_succ hkr) i) :=
  Quotient.inductionOn' j fun _ ↦ rfl

@[simp]
theorem value_truncate {k : ℕ} (hkr : k ≤ r) {x : E} (j : JetAt 𝕜 F r x) :
    value (truncate hkr j) = value j :=
  Quotient.inductionOn' j fun _ ↦ rfl

@[simp]
theorem truncate_rfl {x : E} (j : JetAt 𝕜 F r x) : truncate le_rfl j = j :=
  Quotient.inductionOn' j fun _ ↦ rfl

/-- Truncations compose. -/
@[simp]
theorem truncate_truncate {k l : ℕ} (hlk : l ≤ k) (hkr : k ≤ r) {x : E} (j : JetAt 𝕜 F r x) :
    truncate hlk (truncate hkr j) = truncate (hlk.trans hkr) j :=
  Quotient.inductionOn' j fun _ ↦ rfl

/-- Every jet of order `k ≤ r` lifts to a jet of order `r`: the jet of any representing section. -/
theorem truncate_surjective {k : ℕ} (hkr : k ≤ r) (x : E) :
    Function.Surjective (truncate hkr : JetAt 𝕜 F r x → JetAt 𝕜 F k x) := by
  intro j
  obtain ⟨s, hs, rfl⟩ := exists_section j
  exact ⟨mk s hs, rfl⟩

/-- Jets of order zero are field values, in the selected fibre coordinates. -/
def zeroEquiv (x : E) : JetAt 𝕜 F 0 x ≃ F :=
  Equiv.ofBijective value ⟨fun j k h ↦ ext (funext fun i ↦ by
    rw [Fin.fin_one_eq_zero i, coordinates_zero, coordinates_zero, h]), value_surjective x⟩

@[simp]
theorem zeroEquiv_apply {x : E} (j : JetAt 𝕜 F 0 x) : zeroEquiv x j = value j :=
  (rfl)

open scoped Classical in
/-- Transform a jet by a base change `h` and a base-dependent nonlinear fibre map `g`: the jet of
a section `s` goes to the jet of `y ↦ g (y, s (h y))`, which depends only on the jet of `s`
(`iteratedFDeriv_graph_comp_congr`). When `h` is not smooth at `x` or `g` is not smooth at
`(x, value j)`, the result is, by convention, the jet of the constant section `g (x, value j)`. -/
def map {x : E'} (h : E' → E) (g : E' × F → G) : JetAt 𝕜 F r (h x) → JetAt 𝕜 G r x :=
  Quotient.lift (fun s ↦
    if hsm : ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, s.1 (h x)) then
      mk (fun y ↦ g (y, s.1 (h y))) (hsm.2.comp x (contDiffAt_id.prodMk (s.2.comp x hsm.1)))
    else mk (fun _ ↦ g (x, s.1 (h x))) contDiffAt_const) fun s t hst ↦ by
    have hst' : ∀ k ≤ r, iteratedFDeriv 𝕜 k s.1 (h x) = iteratedFDeriv 𝕜 k t.1 (h x) :=
      fun k hk ↦ congrFun hst ⟨k, Nat.lt_succ_of_le hk⟩
    have hv : s.1 (h x) = t.1 (h x) := by
      simpa using congrArg (fun m ↦ m Fin.elim0) (hst' 0 (Nat.zero_le r))
    simp only [hv]
    split_ifs with hsm
    · exact (mk_eq_mk_iff _ _).2 fun k hk ↦ iteratedFDeriv_graph_comp_congr
        (hsm.1.of_le (mod_cast le_top)) ((hv ▸ hsm.2).of_le (mod_cast le_top))
        (s.2.of_le (mod_cast le_top)) (t.2.of_le (mod_cast le_top)) hst' hk
    · rfl

/-- Computing the jet before or after transforming an actual local section agrees. -/
@[simp]
theorem map_mk {x : E'} (h : E' → E) (g : E' × F → G) (s : E → F)
    (hs : ContDiffAt 𝕜 ∞ s (h x)) (hh : ContDiffAt 𝕜 ∞ h x)
    (hg : ContDiffAt 𝕜 ∞ g (x, s (h x))) :
    map h g (mk s hs : JetAt 𝕜 F r (h x)) =
      mk (fun y ↦ g (y, s (h y))) (hg.comp x (contDiffAt_id.prodMk (hs.comp x hh))) := by
  dsimp only [map, mk, Quotient.mk'', Quotient.lift_mk]
  exact dite_eq_left ⟨hh, hg⟩

/-- Outside the smooth case, `map h g j` is the jet of the constant section `g (x, value j)`: all
its coordinates of positive order vanish. -/
theorem map_of_not_contDiffAt {x : E'} {h : E' → E} {g : E' × F → G} (j : JetAt 𝕜 F r (h x))
    (hsm : ¬(ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, value j))) :
    map h g j = mk (fun _ ↦ g (x, value j)) contDiffAt_const := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  dsimp only [map, mk, Quotient.mk'', Quotient.lift_mk]
  exact dite_eq_right hsm

/-- The value of a transformed jet is the transformed value. This holds unconditionally, also
when `h` or `g` fails to be smooth, by the convention in `map`. -/
@[simp]
theorem value_map {x : E'} (h : E' → E) (g : E' × F → G) (j : JetAt 𝕜 F r (h x)) :
    value (map h g j) = g (x, value j) := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  by_cases hsm : ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, s (h x))
  · rw [map_mk h g s hs hsm.1 hsm.2, value_mk, value_mk]
  · rw [map_of_not_contDiffAt _ hsm, value_mk, value_mk]

/-- Coordinate changes commute with truncation. -/
theorem truncate_map {k : ℕ} (hkr : k ≤ r) {x : E'} (h : E' → E) (g : E' × F → G)
    (j : JetAt 𝕜 F r (h x)) :
    truncate hkr (map h g j) = map h g (truncate hkr j) := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  by_cases hsm : ContDiffAt 𝕜 ∞ h x ∧ ContDiffAt 𝕜 ∞ g (x, s (h x))
  · rw [map_mk h g s hs hsm.1 hsm.2, truncate_mk, truncate_mk, map_mk h g s hs hsm.1 hsm.2]
  · rw [map_of_not_contDiffAt _ hsm, truncate_mk, truncate_mk, map_of_not_contDiffAt _ hsm]
    rfl

/-- The identity coordinate change induces the identity on jets. -/
@[simp]
theorem map_id {x : E} (j : JetAt 𝕜 F r x) : map id Prod.snd j = j := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  exact map_mk (x := x) id Prod.snd s hs contDiffAt_id contDiffAt_snd

/-- Nonlinear changes of coordinates compose on jets. -/
theorem map_comp {y : E''} (h : E' → E) (k : E'' → E') (g : E' × F → G) (l : E'' × G → H)
    (j : JetAt 𝕜 F r (h (k y))) (hh : ContDiffAt 𝕜 ∞ h (k y)) (hk : ContDiffAt 𝕜 ∞ k y)
    (hg : ContDiffAt 𝕜 ∞ g (k y, value j)) (hl : ContDiffAt 𝕜 ∞ l (y, g (k y, value j))) :
    map k l (map h g j) = map (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) j := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  rw [value_mk] at hg hl
  have hgk : ContDiffAt 𝕜 ∞ (fun p : E'' × F ↦ g (k p.1, p.2)) (y, s (h (k y))) :=
    hg.comp (y, s (h (k y))) ((hk.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
  rw [map_mk h g s hs hh hg, map_mk k l _ _ hk hl,
    map_mk (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) s hs (hh.comp y hk)
      (hl.comp (y, s (h (k y))) (contDiffAt_fst.prodMk hgk))]
  rfl

/-- Coordinate changes that are inverse as germs restore the original jet coordinates. The base
points agree by the base germ identity; the coordinate statement avoids transport between the
dependent quotient types at those equal points. -/
theorem coordinates_map_inverse {x : E} (h : E' → E) (k : E → E') (g : E' × F → G)
    (l : E × G → F) (j : JetAt 𝕜 F r (h (k x))) (hh : ContDiffAt 𝕜 ∞ h (k x))
    (hk : ContDiffAt 𝕜 ∞ k x) (hg : ContDiffAt 𝕜 ∞ g (k x, value j))
    (hl : ContDiffAt 𝕜 ∞ l (x, g (k x, value j))) (hbase : h ∘ k =ᶠ[𝓝 x] id)
    (hfibre : (fun p : E × F ↦ l (p.1, g (k p.1, p.2))) =ᶠ[𝓝 (x, value j)] Prod.snd) :
    coordinates (map k l (map h g j)) = coordinates j := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  rw [value_mk] at hg hl hfibre
  have hx : h (k x) = x := hbase.eq_of_nhds
  -- The transformed section is the original one near `x`.
  have hs' : ContDiffAt 𝕜 ∞ s x := hx ▸ hs
  have hloc : (fun y ↦ l (y, g (k y, s (h (k y))))) =ᶠ[𝓝 x] s := by
    have hgraph : Filter.Tendsto (fun y ↦ (y, s y)) (𝓝 x) (𝓝 (x, s (h (k x)))) := by
      rw [hx]
      exact continuousAt_id.prodMk hs'.continuousAt
    filter_upwards [hbase, hgraph.eventually hfibre] with y hy hy'
    simp only [Function.comp_apply, id_eq] at hy
    simpa only [hy] using hy'
  rw [map_mk h g s hs hh hg, map_mk k l _ _ hk hl]
  funext i
  rw [coordinates_mk, coordinates_mk, (hloc.iteratedFDeriv 𝕜 i).eq_of_nhds, hx]

/-- The first jet of the representatives of a jet of order one. -/
private def toFirstJetAt {x : E} : JetAt 𝕜 F 1 x → FirstJetAt 𝕜 F x :=
  Quotient.lift (fun s ↦ FirstJetAt.mk s.1 s.2) fun s t hst ↦
    (FirstJetAt.mk_eq_mk_iff s.2 t.2).2 <| forall_le_one_iteratedFDeriv_eq_iff.1 fun k hk ↦
      congrFun hst ⟨k, Nat.lt_succ_of_le hk⟩

/-- Jets of order one are first jets. -/
def firstJetAtEquiv (x : E) : JetAt 𝕜 F 1 x ≃ FirstJetAt 𝕜 F x :=
  Equiv.ofBijective toFirstJetAt ⟨fun j k hjk ↦ by
    obtain ⟨s, hs, rfl⟩ := exists_section j
    obtain ⟨t, ht, rfl⟩ := exists_section k
    exact (mk_eq_mk_iff hs ht).2 <| forall_le_one_iteratedFDeriv_eq_iff.2 <|
      (FirstJetAt.mk_eq_mk_iff hs ht).1 hjk, fun j ↦ by
    obtain ⟨s, hs, rfl⟩ := FirstJetAt.exists_section j
    exact ⟨mk s hs.contDiffAt, rfl⟩⟩

@[simp]
theorem firstJetAtEquiv_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    firstJetAtEquiv x (mk s hs) = FirstJetAt.mk s hs :=
  (rfl)

@[simp]
theorem value_firstJetAtEquiv {x : E} (j : JetAt 𝕜 F 1 x) :
    (firstJetAtEquiv x j).value = value j := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  rw [firstJetAtEquiv_mk, FirstJetAt.value_mk, value_mk]

/-- The identification of order-one jets with first jets intertwines the coordinate changes. -/
theorem firstJetAtEquiv_map {x : E'} (h : E' → E) (g : E' × F → G) (j : JetAt 𝕜 F 1 (h x))
    (hh : ContDiffAt 𝕜 ∞ h x) (hg : ContDiffAt 𝕜 ∞ g (x, value j)) :
    firstJetAtEquiv x (map h g j) = FirstJetAt.map h g (firstJetAtEquiv (h x) j) := by
  obtain ⟨s, hs, rfl⟩ := exists_section j
  rw [value_mk] at hg
  rw [map_mk h g s hs hh hg, firstJetAtEquiv_mk, firstJetAtEquiv_mk,
    FirstJetAt.map_mk _ _ _ hs hh hg]

end JetAt

end TauCeti
