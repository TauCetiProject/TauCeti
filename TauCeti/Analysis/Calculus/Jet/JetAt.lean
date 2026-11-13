/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.HigherOrder
public import TauCeti.Analysis.Calculus.Jet.Section
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
import TauCeti.Analysis.Calculus.Jet.Realization

/-!
# Higher-order jets of local sections in a bundle chart

`TauCeti.JetAt 𝕜 F r x` is the quotient of maps `E → F` that are `C^∞` near `x` by equality of all
iterated Fréchet derivatives at `x` of order at most `r`. Only the germ at `x` is required to be
smooth, so the quotient applies directly to sections defined on open bundle-chart domains by
extending arbitrarily outside a neighborhood of `x` (`TauCeti.JetAt.mk_eq_mk_of_eventuallyEq`).

Typeclass assumptions follow the exact analytic boundaries of each construction:

* Over any `[NontriviallyNormedField 𝕜]`, we define the quotient `JetAt`, its coordinate map
  `JetAt.coordinates`, order-zero evaluation `JetAt.value`, truncation maps `JetAt.truncate` for
  `r₁ ≤ r₂`, and the equivalences `JetAt.equivZero` (`JetAt 𝕜 F 0 x ≃ F`) and
  `JetAt.equivFirstJetAt` (`JetAt 𝕜 F 1 x ≃ FirstJetAt 𝕜 F x`).
* Over `[CharZero 𝕜]`, every symmetric derivative tuple is realized by a global analytic polynomial
  section (`JetAt.exists_section_coordinates`), whose graph stays inside any prescribed open bundle
  chart around `(x, A 0 0)` near `x` (`JetAt.exists_section_coordinates_mem`).
* Over `[IsRCLikeNormedField 𝕜]` (such as `ℝ` or `ℂ`, where `minSmoothness 𝕜 r = r ≤ ∞` gives
  Schwarz symmetry for `C^∞` germs), `JetAt.coordinatesEquiv` identifies `JetAt 𝕜 F r x` with all
  tuples of slot-symmetric continuous multilinear maps through order `r`, `JetAt.truncate` is
  surjective, and `JetAt.map` implements nonlinear base-and-fibre coordinate transformations via
  `TauCeti.jetCoordChange`, satisfying the section chain rule, truncation naturality, identity,
  cocycle, and local germ-inverse laws.

No vector-space structure is selected intrinsically on `JetAt 𝕜 F r x`, and no global manifold jet
bundle is constructed here.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A.
* Ivan Kolář, Peter W. Michor and Jan Slovák, *Natural Operations in Differential Geometry*,
  Chapter 12.
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

/-- Order-`r` jets at `x` of local smooth sections in a bundle chart with base `E` and fibre `F`.
Two maps that are `C^∞` at `x` represent the same `r`-jet when all their iterated derivatives at
`x` through order `r` agree. -/
def JetAt (𝕜 : Type*) {E : Type*} (F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (r : ℕ) (x : E) :=
  Quotient (Setoid.ker (fun s : {s : E → F // ContDiffAt 𝕜 ∞ s x} ↦
    fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s.1 x))

namespace JetAt

/-! ### Quotient interface, value, and truncation -/

/-- The `r`-jet at `x` of a map `s` that is `C^∞` at `x`. -/
def mk (r : ℕ) {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) : JetAt 𝕜 F r x :=
  Quotient.mk'' ⟨s, hs⟩

/-- Derivative coordinates through order `r` of an `r`-jet in the chosen bundle chart. -/
def coordinates {r : ℕ} {x : E} :
    JetAt 𝕜 F r x → ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :=
  Setoid.kerLift _

@[simp]
theorem coordinates_mk (r : ℕ) {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    coordinates (mk r s hs) = fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s x :=
  (rfl)

/-- Two local smooth sections define the same `r`-jet at `x` if and only if their iterated
derivatives at `x` agree in every order `i ≤ r`. -/
@[simp]
theorem mk_eq_mk_iff {r : ℕ} {x : E} {s t : E → F}
    (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x) :
    mk r s hs = mk r t ht ↔ ∀ i : Fin (r + 1),
      iteratedFDeriv 𝕜 i.val s x = iteratedFDeriv 𝕜 i.val t x := by
  constructor
  · intro h i
    exact congrFun (congrArg coordinates h) i
  · intro h
    exact Quotient.sound (funext h)

/-- An `r`-jet depends only on the germ of a representative section at `x`. -/
theorem mk_eq_mk_of_eventuallyEq (r : ℕ) {x : E} {s t : E → F}
    (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x) (h : s =ᶠ[𝓝 x] t) :
    mk r s hs = mk r t ht :=
  (mk_eq_mk_iff hs ht).mpr fun i ↦ (h.iteratedFDeriv 𝕜 i.val).eq_of_nhds

/-- An `r`-jet is uniquely determined by its coordinate tuple. -/
@[ext]
theorem ext {r : ℕ} {x : E} {j k : JetAt 𝕜 F r x} (h : coordinates j = coordinates k) :
    j = k :=
  Setoid.kerLift_injective _ h

/-- Order-zero field value of an `r`-jet in the selected fibre coordinates. -/
def value {r : ℕ} {x : E} (j : JetAt 𝕜 F r x) : F :=
  coordinates j 0 0

theorem coordinates_zero_apply {r : ℕ} {x : E} (j : JetAt 𝕜 F r x)
    (v : Fin (0 : Fin (r + 1)).val → E) :
    coordinates j 0 v = value j :=
  congrArg (coordinates j 0) (funext fun k ↦ Fin.elim0 k)

@[simp]
theorem value_mk (r : ℕ) {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    value (mk r s hs) = s x :=
  (rfl)

/-- Order-zero evaluation is surjective in every order `r`, realized by constant sections. -/
theorem value_surjective (r : ℕ) (x : E) :
    Function.Surjective (value : JetAt 𝕜 F r x → F) := fun v ↦
  ⟨mk r (fun _ ↦ v) contDiffAt_const, rfl⟩

/-- Truncate an `r₂`-jet at `x` to an `r₁`-jet at `x` for `r₁ ≤ r₂`. -/
def truncate {r₁ r₂ : ℕ} {x : E} (hle : r₁ ≤ r₂) : JetAt 𝕜 F r₂ x → JetAt 𝕜 F r₁ x :=
  Quotient.lift (fun s ↦ mk r₁ s.1 s.2) fun a b hab ↦
    (mk_eq_mk_iff a.2 b.2).mpr fun i ↦ congrFun hab (i.castLE (Nat.add_le_add_right hle 1))

@[simp]
theorem truncate_mk {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) {x : E} (s : E → F)
    (hs : ContDiffAt 𝕜 ∞ s x) :
    truncate hle (mk r₂ s hs) = mk r₁ s hs :=
  (rfl)

@[simp]
theorem coordinates_truncate {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) {x : E} (j : JetAt 𝕜 F r₂ x) :
    coordinates (truncate hle j) = jetTruncate hle (coordinates j) := by
  refine Quotient.inductionOn j fun _ ↦ funext fun _ ↦ ?_
  rw [jetTruncate_apply]
  rfl

@[simp]
theorem value_truncate {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) {x : E} (j : JetAt 𝕜 F r₂ x) :
    value (truncate hle j) = value j :=
  Quotient.inductionOn j fun _ ↦ rfl

@[simp]
theorem truncate_refl {r : ℕ} {x : E} (j : JetAt 𝕜 F r x) :
    truncate (le_refl r) j = j :=
  Quotient.inductionOn j fun _ ↦ rfl

theorem truncate_trans {r₁ r₂ r₃ : ℕ} (h₁₂ : r₁ ≤ r₂) (h₂₃ : r₂ ≤ r₃)
    {x : E} (j : JetAt 𝕜 F r₃ x) :
    truncate h₁₂ (truncate h₂₃ j) = truncate (h₁₂.trans h₂₃) j :=
  Quotient.inductionOn j fun _ ↦ rfl

/-! ### Identification at orders `0` and `1` -/

variable (𝕜) in
/-- Order-zero jets at `x` identify canonically with fibre values `F`. -/
def equivZero (x : E) : JetAt 𝕜 F 0 x ≃ F where
  toFun := value
  invFun v := mk 0 (fun _ ↦ v) contDiffAt_const
  left_inv j := by
    refine ext (funext fun i ↦ ?_)
    have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst hi
    ext w
    dsimp only
    rw [coordinates_zero_apply, coordinates_zero_apply, value_mk]
  right_inv _ := rfl

@[simp]
theorem equivZero_apply {x : E} (j : JetAt 𝕜 F 0 x) :
    equivZero 𝕜 x j = value j :=
  (rfl)

@[simp]
theorem equivZero_symm_apply {x : E} (v : F) :
    (equivZero 𝕜 x).symm v = mk 0 (fun _ ↦ v) contDiffAt_const :=
  (rfl)

/-- Order-one jets in `JetAt` identify canonically with `TauCeti.FirstJetAt`. -/
def equivFirstJetAt (x : E) : JetAt 𝕜 F 1 x ≃ FirstJetAt 𝕜 F x where
  toFun j := (FirstJetAt.coordinatesEquiv x).symm
    (value j, continuousMultilinearCurryFin1 𝕜 E F (coordinates j 1))
  invFun j := mk 1 (FirstJetAt.exists_section_coordinates x j.coordinates).choose
    (FirstJetAt.exists_section_coordinates x j.coordinates).choose_spec.1.contDiffAt
  left_inv j := by
    have hs := ((FirstJetAt.exists_section_coordinates x
      ((FirstJetAt.coordinatesEquiv x).symm
        (value j, continuousMultilinearCurryFin1 𝕜 E F
          (coordinates j 1))).coordinates).choose_spec.2).trans
      (FirstJetAt.coordinates_coordinatesEquiv_symm x _)
    obtain ⟨hsv, hsd⟩ := Prod.ext_iff.mp hs
    refine ext (funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩))
    · ext w
      dsimp only
      rw [coordinates_zero_apply, coordinates_zero_apply, value_mk]
      exact hsv
    · apply (continuousMultilinearCurryFin1 𝕜 E F).injective
      simpa [coordinates_mk, continuousMultilinearCurryFin1_iteratedFDeriv_one] using hsd
  right_inv j := by
    apply FirstJetAt.ext
    rw [FirstJetAt.coordinates_coordinatesEquiv_symm]
    have hs := (FirstJetAt.exists_section_coordinates x j.coordinates).choose_spec.2
    obtain ⟨hsv, hsd⟩ := Prod.ext_iff.mp hs
    refine Prod.ext hsv ?_
    simpa [coordinates_mk, continuousMultilinearCurryFin1_iteratedFDeriv_one] using hsd

@[simp]
theorem coordinates_equivFirstJetAt {x : E} (j : JetAt 𝕜 F 1 x) :
    FirstJetAt.coordinates (equivFirstJetAt x j) =
      (value j, continuousMultilinearCurryFin1 𝕜 E F (coordinates j 1)) := by
  dsimp [equivFirstJetAt]
  exact FirstJetAt.coordinates_coordinatesEquiv_symm x _

@[simp]
theorem value_equivFirstJetAt {x : E} (j : JetAt 𝕜 F 1 x) :
    FirstJetAt.value (equivFirstJetAt x j) = value j := by
  rw [← FirstJetAt.fst_coordinates, coordinates_equivFirstJetAt]

@[simp]
theorem equivFirstJetAt_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    equivFirstJetAt x (mk 1 s hs) = FirstJetAt.mk s hs := by
  apply FirstJetAt.ext
  rw [coordinates_equivFirstJetAt, FirstJetAt.coordinates_mk]
  exact Prod.ext rfl (continuousMultilinearCurryFin1_iteratedFDeriv_one s x)

@[simp]
theorem equivFirstJetAt_symm_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    (equivFirstJetAt x).symm (FirstJetAt.mk s hs) = mk 1 s hs :=
  (equivFirstJetAt x).injective (by simp)

/-! ### Polynomial realization and symmetric coordinate equivalence -/

/-- Over a field of characteristic zero, every tuple of slot-symmetric multilinear maps through
order `r` is the coordinate tuple of a global `C^∞` polynomial section. -/
theorem exists_section_coordinates [CharZero 𝕜] (r : ℕ) (x : E)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v) :
    ∃ s : E → F, ContDiff 𝕜 ∞ s ∧
      (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s x) = A :=
  ⟨finiteJetPolynomial r A x, contDiff_finiteJetPolynomial r A x,
    funext fun i ↦ iteratedFDeriv_finiteJetPolynomial_self r A x i (hA i)⟩

/-- Over a field of characteristic zero, a prescribed symmetric `r`-jet whose value lies in an
open bundle-chart domain `u` is realized by a global `C^∞` section whose graph remains in `u`
near `x`. -/
theorem exists_section_coordinates_mem [CharZero 𝕜] (r : ℕ) {x : E}
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v)
    {u : Set (E × F)} (hu : IsOpen u) (hmem : (x, A 0 0) ∈ u) :
    ∃ s : E → F, ContDiff 𝕜 ∞ s ∧
      (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s x) = A ∧
      ∀ᶠ y in 𝓝 x, (y, s y) ∈ u := by
  obtain ⟨s, hs, hsA, hsu⟩ :=
    exists_contDiff_iteratedFDeriv_eq_eventually_mem r A hA x (hu.mem_nhds hmem)
  exact ⟨s, hs.of_le (by simp), funext hsA, hsu⟩

/-- Over `ℝ` or `ℂ` (`IsRCLikeNormedField 𝕜`), every coordinate of a local `r`-jet is symmetric
under arbitrary permutations of its multilinear slots. -/
theorem coordinates_comp_perm [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E} (j : JetAt 𝕜 F r x)
    (i : Fin (r + 1)) (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)) :
    coordinates j i (v ∘ σ) = coordinates j i v := by
  refine Quotient.inductionOn j (fun s ↦ ?_)
  exact s.2.iteratedFDeriv_comp_perm_of_minSmoothness
    (by rw [minSmoothness_of_isRCLikeNormedField]; simp) v σ

/-- Over `ℝ` or `ℂ`, `JetAt.coordinates` identifies `r`-jets at `x` bijectively with all tuples of
slot-symmetric continuous multilinear maps through order `r`. This identification depends on the
selected bundle chart. -/
def coordinatesEquiv [IsRCLikeNormedField 𝕜] (r : ℕ) (x : E) :
    JetAt 𝕜 F r x ≃
      {A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F //
        ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v} where
  toFun j := ⟨coordinates j, coordinates_comp_perm j⟩
  invFun A := mk r (finiteJetPolynomial r A.1 x) (contDiff_finiteJetPolynomial r A.1 x).contDiffAt
  left_inv j := by
    let := IsRCLikeNormedField.rclike 𝕜
    refine ext (funext fun i ↦ ?_)
    exact iteratedFDeriv_finiteJetPolynomial_self r (coordinates j) x i (coordinates_comp_perm j i)
  right_inv A := by
    let := IsRCLikeNormedField.rclike 𝕜
    refine Subtype.ext (funext fun i ↦ ?_)
    exact iteratedFDeriv_finiteJetPolynomial_self r A.1 x i (A.2 i)

@[simp]
theorem coe_coordinatesEquiv_apply [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E}
    (j : JetAt 𝕜 F r x) :
    ((coordinatesEquiv r x j :
      {_A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F // _}) :
        (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) = coordinates j :=
  (rfl)

@[simp]
theorem coordinates_coordinatesEquiv_symm [IsRCLikeNormedField 𝕜] (r : ℕ) (x : E)
    (A : {A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F //
      ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v}) :
    coordinates ((coordinatesEquiv r x).symm A) = A.1 :=
  congrArg Subtype.val ((coordinatesEquiv r x).apply_symm_apply A)

/-- Over `ℝ` or `ℂ`, every `r`-jet class has a globally `C^∞` representative on the base chart. -/
theorem exists_section [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E} (j : JetAt 𝕜 F r x) :
    ∃ s : E → F, ∃ hs : ContDiff 𝕜 ∞ s, mk r s hs.contDiffAt = j := by
  let := IsRCLikeNormedField.rclike 𝕜
  obtain ⟨s, hs, hj⟩ := exists_section_coordinates r x (coordinates j) (coordinates_comp_perm j)
  exact ⟨s, hs, ext hj⟩

/-- Over `ℝ` or `ℂ`, jet truncation `JetAt 𝕜 F r₂ x → JetAt 𝕜 F r₁ x` is surjective
for `r₁ ≤ r₂`. -/
theorem truncate_surjective [IsRCLikeNormedField 𝕜] {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) (x : E) :
    Function.Surjective (truncate hle : JetAt 𝕜 F r₂ x → JetAt 𝕜 F r₁ x) := by
  intro j
  obtain ⟨s, hs, rfl⟩ := exists_section j
  exact ⟨mk r₂ s hs.contDiffAt, rfl⟩

/-! ### Nonlinear bundle coordinate transformations on `JetAt` -/

/-- Transform an `r`-jet at `h x` along a base map `h : E' → E` and a possibly nonlinear,
base-dependent fibre map `g : E' × F → G`. When `h` is `C^r` at `x` and `g` is `C^r` at
`(x, j.value)`, the output has coordinates `TauCeti.jetCoordChange r h g x (coordinates j)`. -/
def map [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E'} (h : E' → E) (g : E' × F → G)
    (j : JetAt 𝕜 F r (h x)) : JetAt 𝕜 G r x :=
  open Classical in
  if hhg : ContDiffAt 𝕜 r h x ∧ ContDiffAt 𝕜 r g (x, value j) then
    (coordinatesEquiv r x).symm ⟨jetCoordChange r h g x (coordinates j),
      jetCoordChange_comp_perm_of_isRCLikeNormedField hhg.1 hhg.2 (coordinates_comp_perm j)⟩
  else
    mk r (fun _ ↦ g (x, value j)) contDiffAt_const

/-- For `C^r` coordinate maps, `JetAt.map` acts on coordinates by `TauCeti.jetCoordChange`. -/
@[simp]
theorem coordinates_map [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E'}
    {h : E' → E} {g : E' × F → G} (j : JetAt 𝕜 F r (h x))
    (hh : ContDiffAt 𝕜 r h x) (hg : ContDiffAt 𝕜 r g (x, value j)) :
    coordinates (map h g j) = jetCoordChange r h g x (coordinates j) := by
  have hhg : ContDiffAt 𝕜 r h x ∧ ContDiffAt 𝕜 r g (x, value j) := ⟨hh, hg⟩
  simp [map, hhg]

@[simp]
theorem value_map [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E'}
    (h : E' → E) (g : E' × F → G) (j : JetAt 𝕜 F r (h x)) :
    value (map h g j) = g (x, value j) := by
  by_cases hhg : ContDiffAt 𝕜 r h x ∧ ContDiffAt 𝕜 r g (x, value j)
  · rw [value, coordinates_map j hhg.1 hhg.2]
    exact jetCoordChange_zero_apply r h g x (coordinates j) 0
  · simp [map, hhg]

/-- Computing the `r`-jet before or after transforming a smooth local section gives the same
`r`-jet. -/
@[simp]
theorem map_mk [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E'}
    (h : E' → E) (g : E' × F → G) (s : E → F)
    (hs : ContDiffAt 𝕜 ∞ s (h x)) (hh : ContDiffAt 𝕜 ∞ h x)
    (hg : ContDiffAt 𝕜 ∞ g (x, s (h x))) :
    map h g (mk r s hs) =
      mk r (fun y ↦ g (y, s (h y))) (hg.comp x (contDiffAt_id.prodMk (hs.comp x hh))) := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by simp
  apply ext
  rw [coordinates_map (mk r s hs) (hh.of_le hr) (hg.of_le hr), coordinates_mk, coordinates_mk]
  exact jetCoordChange_iteratedFDeriv (hh.of_le hr) (hs.of_le hr) (hg.of_le hr)

/-- Nonlinear coordinate transformations on `JetAt` commute with truncation to any lower order. -/
theorem truncate_map [IsRCLikeNormedField 𝕜] {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) {x : E'}
    {h : E' → E} {g : E' × F → G} (j : JetAt 𝕜 F r₂ (h x))
    (hh : ContDiffAt 𝕜 r₂ h x) (hg : ContDiffAt 𝕜 r₂ g (x, value j)) :
    truncate hle (map h g j) = map h g (truncate hle j) := by
  have hr : (r₁ : ℕ∞ω) ≤ r₂ := Nat.cast_le.mpr hle
  have hg₁ : ContDiffAt 𝕜 r₁ g (x, value (truncate hle j)) := by
    simpa only [value_truncate] using hg.of_le hr
  apply ext
  rw [coordinates_truncate, coordinates_map j hh hg,
    coordinates_map (truncate hle j) (hh.of_le hr) hg₁, coordinates_truncate,
    jetTruncate_jetCoordChange]

/-- At order `1`, `JetAt.map` agrees with `FirstJetAt.map` under `JetAt.equivFirstJetAt`. -/
theorem equivFirstJetAt_map [IsRCLikeNormedField 𝕜] {x : E'}
    {h : E' → E} {g : E' × F → G} (j : JetAt 𝕜 F 1 (h x))
    (hh : ContDiffAt 𝕜 1 h x) (hg : ContDiffAt 𝕜 1 g (x, value j)) :
    equivFirstJetAt x (map h g j) = FirstJetAt.map h g (equivFirstJetAt (h x) j) := by
  apply FirstJetAt.ext
  rw [coordinates_equivFirstJetAt, FirstJetAt.coordinates_map, coordinates_equivFirstJetAt]
  dsimp only [value]
  rw [coordinates_map j hh hg]
  exact (firstJetCoordChange_eq_jetCoordChange h g x (coordinates j)).symm

/-- Identity base and fibre coordinate maps induce the identity on `r`-jets. -/
@[simp]
theorem map_id [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E} (j : JetAt 𝕜 F r x) :
    map id Prod.snd j = j := by
  apply ext
  rw [coordinates_map j contDiffAt_id contDiffAt_snd, jetCoordChange_id]

/-- Nonlinear bundle coordinate changes compose on `r`-jet section classes. -/
theorem map_comp [IsRCLikeNormedField 𝕜] {r : ℕ} {y : E''}
    (h : E' → E) (k : E'' → E') (g : E' × F → G) (l : E'' × G → H)
    (j : JetAt 𝕜 F r (h (k y)))
    (hh : ContDiffAt 𝕜 r h (k y)) (hk : ContDiffAt 𝕜 r k y)
    (hg : ContDiffAt 𝕜 r g (k y, value j))
    (hl : ContDiffAt 𝕜 r l (y, g (k y, value j))) :
    map k l (map h g j) =
      map (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) j := by
  have hl' : ContDiffAt 𝕜 r l (y, value (map h g j)) := by
    simpa only [value_map] using hl
  have hfg : ContDiffAt 𝕜 r (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) (y, value j) :=
    hl.comp (y, value j)
      (contDiffAt_fst.prodMk (hg.comp (y, value j)
        ((hk.comp (y, value j) contDiffAt_fst).prodMk contDiffAt_snd)))
  apply ext
  rw [coordinates_map (map h g j) hk hl', coordinates_map j hh hg,
    coordinates_map (x := y) (h := h ∘ k) j (hh.comp y hk) hfg]
  exact jetCoordChange_comp (coordinates j) hh hk hg hl

/-- Coordinate maps that are inverse as germs restore the original `r`-jet coordinates. -/
theorem coordinates_map_inverse [IsRCLikeNormedField 𝕜] {r : ℕ} {x : E}
    (h : E' → E) (k : E → E') (g : E' × F → G) (l : E × G → F)
    (j : JetAt 𝕜 F r (h (k x)))
    (hh : ContDiffAt 𝕜 r h (k x)) (hk : ContDiffAt 𝕜 r k x)
    (hg : ContDiffAt 𝕜 r g (k x, value j))
    (hl : ContDiffAt 𝕜 r l (x, g (k x, value j)))
    (hbase : h ∘ k =ᶠ[𝓝 x] id)
    (hfibre : (fun p : E × F ↦ l (p.1, g (k p.1, p.2))) =ᶠ[𝓝 (x, value j)] Prod.snd) :
    coordinates (map k l (map h g j)) = coordinates j := by
  have hl' : ContDiffAt 𝕜 r l (x, value (map h g j)) := by
    simpa only [value_map] using hl
  rw [coordinates_map (map h g j) hk hl', coordinates_map j hh hg]
  exact jetCoordChange_inverse (coordinates j) hh hk hg hl hbase hfibre

end JetAt

end TauCeti
