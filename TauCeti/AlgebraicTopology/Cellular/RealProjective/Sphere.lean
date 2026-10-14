/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Sphere.Puncture

/-!
# The collapse map from real projective space to the sphere

Collapsing `RPⁿ⁻¹ ⊆ RPⁿ` to a point gives the sphere: the top cell of the CW structure on `RPⁿ`
(`TauCeti.RealProjectiveSpace.cwComplex`) is an open `n`-ball whose closure adds only `RPⁿ⁻¹`. This
file writes the collapse explicitly as the map

`TauCeti.RealProjectiveSpace.toSphere : RPⁿ ⟶ Sⁿ`, `[v] ↦ 2 vₙ v - eₙ`,

which is well defined because the formula is even in `v`. It sends exactly the classes with
`vₙ = 0`, that is `RPⁿ⁻¹`, to `-eₙ`
(`TauCeti.RealProjectiveSpace.coe_toSphere_mk_eq_neg_single_iff`), and on the open top cell it is
a homeomorphism onto `Sⁿ ∖ {-eₙ}` with inverse `w ↦ [(w + eₙ) / ‖w + eₙ‖]`.

The main result computes its effect on top homology in characteristic `2`
(`TauCeti.RealProjectiveSpace.isIso_singularHomologyMap_toSphere`): for a ring `R` with `2 = 0`,
`Hₙ₊₁(RPⁿ⁺¹; R) ⟶ Hₙ₊₁(Sⁿ⁺¹; R)` is an isomorphism. Integrally the two groups differ (for even
`n + 1` the first vanishes), so the collapse map `RP² ⟶ S²` induces zero on integral homology in
degrees one and two but an isomorphism on `H₂(-; ℤ/2)`. This is the input to the standard proof
that the splitting of the universal coefficient sequence for cohomology cannot be chosen naturally.

The proof reads both top homology groups in the local homology at `[eₙ₊₁]` and at its image `eₙ₊₁`.

* In characteristic `2` the top cellular differential of `RPⁿ⁺¹` vanishes, being twice a unit or
  zero (`TauCeti.RealProjectiveSpace.cellularChainComplex_d_eq_zero_of_two_eq_zero`), so the
  top homology of `RPⁿ⁺¹` is the chain group of its single top cell. That cell computes the local
  homology at any point of its open cell (`TauCeti.isIso_cellLocalClass`).
* The punctured sphere is contractible, so `Hₙ₊₁(Sⁿ⁺¹) ⟶ Hₙ₊₁(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {eₙ₊₁})` is an
  isomorphism.
* The collapse map is a homeomorphism near `[eₙ₊₁]`, and `[eₙ₊₁]` is the only point over `eₙ₊₁`,
  so by excision it induces an isomorphism of local homology
  (`TauCeti.singularHomologyComplSingletonIsoOfChart`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Example 0.4 for the cells of `RPⁿ`, Example 2.42 for its cellular boundary, and Section 3.1 for
  the universal coefficient theorem.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti.RealProjectiveSpace

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The point `2 vₙ v - eₙ` of the unit sphere, for a unit vector `v`. -/
private def toSphereAux (v : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨(2 * (v : E) (Fin.last n)) • (v : E) - EuclideanSpace.single (Fin.last n) 1, by
    have hv : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.1 v.2
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      norm_sub_sq_real, norm_smul, inner_smul_left, EuclideanSpace.inner_single_right,
      PiLp.norm_single, hv]
    simp only [Real.norm_eq_abs, mul_one, one_mul, norm_one, conj_trivial, sq_abs]
    ring⟩

private theorem continuous_toSphereAux : Continuous (toSphereAux n) := by
  unfold toSphereAux
  fun_prop

private theorem toSphereAux_neg (v : sphere (0 : E) 1) : toSphereAux n (-v) = toSphereAux n v := by
  ext1
  simp [toSphereAux, coe_neg_sphere]

/-- **The collapse map `RPⁿ ⟶ Sⁿ`**, `[v] ↦ 2 vₙ v - eₙ`. It collapses `RPⁿ⁻¹`, the classes
with `vₙ = 0`, to the point `-eₙ`
(`TauCeti.RealProjectiveSpace.coe_toSphere_mk_eq_neg_single_iff`), and maps the open top cell
`RPⁿ ∖ RPⁿ⁻¹` homeomorphically onto `Sⁿ ∖ {-eₙ}`; so it identifies `RPⁿ / RPⁿ⁻¹` with `Sⁿ`. -/
def toSphere : C(RealProjectiveSpace n, sphere (0 : E) 1) where
  toFun := RealProjectiveSpace.lift n (toSphereAux n) (toSphereAux_neg n)
  continuous_toFun := (isQuotientMap_mk n).continuous_iff.2 <|
    (continuous_toSphereAux n).congr fun v ↦
      (RealProjectiveSpace.lift_mk n (toSphereAux n) (toSphereAux_neg n) v).symm

@[simp]
theorem coe_toSphere_mk (v : sphere (0 : E) 1) :
    (toSphere n (mk n v) : E) =
      (2 * (v : E) (Fin.last n)) • (v : E) - EuclideanSpace.single (Fin.last n) 1 :=
  congrArg Subtype.val (RealProjectiveSpace.lift_mk n (toSphereAux n) (toSphereAux_neg n) v)

/-- The collapse map sends exactly the classes of `RPⁿ⁻¹`, those with `vₙ = 0`, to `-eₙ`. -/
theorem coe_toSphere_mk_eq_neg_single_iff (v : sphere (0 : E) 1) :
    (toSphere n (mk n v) : E) = -EuclideanSpace.single (Fin.last n) 1 ↔
      (v : E) (Fin.last n) = 0 := by
  have hv : (v : E) ≠ 0 := ne_zero_of_mem_unit_sphere v
  rw [coe_toSphere_mk, sub_eq_neg_self, smul_eq_zero, or_iff_left hv, mul_eq_zero,
    or_iff_right two_ne_zero]

/-- The collapse map sends only the class of `±eₙ` to `eₙ`. -/
theorem coe_toSphere_mk_eq_single_iff (v : sphere (0 : E) 1) :
    (toSphere n (mk n v) : E) = EuclideanSpace.single (Fin.last n) 1 ↔
      (v : E) = EuclideanSpace.single (Fin.last n) 1 ∨
        (v : E) = -EuclideanSpace.single (Fin.last n) 1 := by
  rw [coe_toSphere_mk, sub_eq_iff_eq_add, ← two_smul ℝ, mul_smul,
    smul_right_inj (two_ne_zero' ℝ)]
  constructor
  · intro h
    -- Reading off coordinate `n` gives `vₙ² = 1`.
    have hn := congrArg (fun w : E ↦ w (Fin.last n)) h
    simp only [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, ite_true] at hn
    rcases mul_self_eq_one_iff.1 hn with h1 | h1
    · left
      rwa [h1, one_smul] at h
    · right
      rw [h1, neg_one_smul, neg_eq_iff_eq_neg] at h
      exact h
  · rintro (h | h) <;> rw [h] <;> simp

/-! ### The collapse map near `eₙ` -/

/-- The unit vector `eₙ`, as a point of the unit sphere. -/
private def singleLast : sphere (0 : E) 1 :=
  ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩

@[simp]
private theorem coe_singleLast :
    (singleLast n : E) = EuclideanSpace.single (Fin.last n) 1 :=
  (rfl)

/-- `‖w + eₙ‖² = 2 (1 + wₙ)` for a unit vector `w`. -/
private theorem norm_add_single_sq (w : sphere (0 : E) 1) :
    ‖(w : E) + EuclideanSpace.single (Fin.last n) 1‖ ^ 2 = 2 * (1 + (w : E) (Fin.last n)) := by
  rw [norm_add_sq_real, EuclideanSpace.inner_single_right, PiLp.norm_single,
    mem_sphere_zero_iff_norm.1 w.2]
  simp only [one_mul, norm_one, conj_trivial]
  ring

/-- The local inverse of the collapse map on `Sⁿ ∖ {-eₙ}`: `w ↦ [(w + eₙ) / ‖w + eₙ‖]`. Its value
at `-eₙ` is irrelevant. -/
private def toSphereInv (w : sphere (0 : E) 1) : RealProjectiveSpace n :=
  if hw : (w : E) + EuclideanSpace.single (Fin.last n) 1 = 0 then mk n w else
    mk n ⟨‖(w : E) + EuclideanSpace.single (Fin.last n) 1‖⁻¹ •
      ((w : E) + EuclideanSpace.single (Fin.last n) 1), by
        rw [mem_sphere_zero_iff_norm]
        exact norm_smul_inv_norm hw⟩

private theorem toSphere_toSphereInv {w : sphere (0 : E) 1}
    (hw : (w : E) + EuclideanSpace.single (Fin.last n) 1 ≠ 0) :
    toSphere n (toSphereInv n w) = w := by
  set s := (w : E) + EuclideanSpace.single (Fin.last n) 1
  have hs : ‖s‖ ^ 2 = 2 * (1 + (w : E) (Fin.last n)) := norm_add_single_sq n w
  have hs0 : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hw
  ext1
  rw [toSphereInv, dite_eq_right_of_eq_false (eq_false hw), coe_toSphere_mk]
  simp only [PiLp.smul_apply, smul_eq_mul, PiLp.add_apply, PiLp.single_apply, ite_true,
    smul_smul]
  -- The scalar `2 ‖s‖⁻¹ (wₙ + 1) ‖s‖⁻¹` is `1`, since `‖s‖² = 2 (1 + wₙ)`.
  have : 2 * (‖s‖⁻¹ * ((w : E) (Fin.last n) + 1)) * ‖s‖⁻¹ = 1 := by
    field_simp
    linarith
  rw [this, one_smul, add_sub_cancel_right]

private theorem toSphereInv_toSphere {p : RealProjectiveSpace n}
    (hp : (toSphere n p : E) + EuclideanSpace.single (Fin.last n) 1 ≠ 0) :
    toSphereInv n (toSphere n p) = p := by
  induction p using RealProjectiveSpace.inductionOn with | h v => ?_
  have hvn : (v : E) (Fin.last n) ≠ 0 := fun h ↦
    hp (by rw [(coe_toSphere_mk_eq_neg_single_iff n v).2 h, neg_add_cancel])
  rw [toSphereInv, dite_eq_right_of_eq_false (eq_false hp), mk_eq_mk_iff]
  -- `toSphere (mk v) + eₙ = 2 vₙ v`, whose normalisation is `± v` according to the sign of `vₙ`.
  have hs : (toSphere n (mk n v) : E) + EuclideanSpace.single (Fin.last n) 1 =
      (2 * (v : E) (Fin.last n)) • (v : E) := by
    rw [coe_toSphere_mk, sub_add_cancel]
  have hnorm : ‖(2 * (v : E) (Fin.last n)) • (v : E)‖ = |2 * (v : E) (Fin.last n)| := by
    rw [norm_smul, mem_sphere_zero_iff_norm.1 v.2, mul_one, Real.norm_eq_abs]
  simp only [Subtype.ext_iff, coe_neg_sphere, hs, hnorm, smul_smul]
  rcases hvn.lt_or_gt with h | h
  · right
    rw [abs_of_neg (by linarith), inv_mul_eq_div, div_neg, div_self (by positivity), neg_one_smul]
  · left
    rw [abs_of_pos (by linarith), inv_mul_eq_div, div_self (by positivity), one_smul]

private theorem continuousOn_toSphereInv :
    ContinuousOn (toSphereInv n) {w | (w : E) + EuclideanSpace.single (Fin.last n) 1 ≠ 0} := by
  set T := {w : sphere (0 : E) 1 | (w : E) + EuclideanSpace.single (Fin.last n) 1 ≠ 0}
  let s : T → E := fun w ↦ ((w : sphere (0 : E) 1) : E) + EuclideanSpace.single (Fin.last n) 1
  have hs : Continuous s := by fun_prop
  have hs0 (w : T) : s w ≠ 0 := w.2
  -- On `T`, the local inverse is the class of the normalisation of `w + eₙ`.
  let g : T → sphere (0 : E) 1 := fun w ↦ ⟨‖s w‖⁻¹ • s w, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (hs0 w)⟩
  have hg : Continuous g :=
    ((hs.norm.inv₀ fun w ↦ norm_ne_zero_iff.2 (hs0 w)).smul hs).subtype_mk _
  have heq : T.domRestrict (toSphereInv n) = mk n ∘ g :=
    funext fun w ↦ dite_eq_right_of_eq_false (eq_false (hs0 w))
  rw [continuousOn_iff_continuous_domRestrict, heq]
  exact (continuous_mk n).comp hg

/-- The collapse map as an open partial homeomorphism from `RPⁿ ∖ RPⁿ⁻¹` onto `Sⁿ ∖ {-eₙ}`. -/
private def toSphereChart : OpenPartialHomeomorph (RealProjectiveSpace n) (sphere (0 : E) 1) where
  toFun := toSphere n
  invFun := toSphereInv n
  source := toSphere n ⁻¹' {w | (w : E) + EuclideanSpace.single (Fin.last n) 1 ≠ 0}
  target := {w | (w : E) + EuclideanSpace.single (Fin.last n) 1 ≠ 0}
  map_source' _ hp := hp
  map_target' w hw := by
    rw [Set.mem_preimage, toSphere_toSphereInv n hw]
    exact hw
  left_inv' _ hp := toSphereInv_toSphere n hp
  right_inv' _ hw := toSphere_toSphereInv n hw
  open_source := (isOpen_ne_fun (by fun_prop) continuous_const).preimage (toSphere n).continuous
  open_target := isOpen_ne_fun (by fun_prop) continuous_const
  continuousOn_toFun := (toSphere n).continuous.continuousOn
  continuousOn_invFun := continuousOn_toSphereInv n

@[simp]
private theorem toSphereChart_apply (p : RealProjectiveSpace n) :
    toSphereChart n p = toSphere n p :=
  (rfl)

/-- The class of `eₙ`, the centre of the open top cell of `RPⁿ`. -/
private abbrev basePoint : RealProjectiveSpace n :=
  mk n (singleLast n)

private theorem toSphere_basePoint : toSphere n (basePoint n) = singleLast n := by
  ext1
  simp [basePoint, two_smul]

private theorem basePoint_mem_source : basePoint n ∈ (toSphereChart n).source := by
  -- Membership in the source of the chart is, by its definition, the inequality below.
  change (toSphere n (basePoint n) : E) + EuclideanSpace.single (Fin.last n) 1 ≠ 0
  rw [toSphere_basePoint, coe_singleLast, ← two_smul ℝ]
  exact smul_ne_zero two_ne_zero (by simp)

/-- Only `[eₙ]` is sent to `eₙ` by the collapse map. -/
private theorem mapsTo_toSphere_compl :
    MapsTo (TopCat.ofHom (toSphere n)) ({basePoint n}ᶜ : Set (TopCat.of (RealProjectiveSpace n)))
      ({toSphereChart n (basePoint n)}ᶜ : Set (TopCat.of (sphere (0 : E) 1))) := by
  intro p hp hq
  refine hp ?_
  induction p using RealProjectiveSpace.inductionOn with | h v => ?_
  rw [Set.mem_singleton_iff, TopCat.ofHom_apply, toSphereChart_apply, toSphere_basePoint] at hq
  rw [Set.mem_singleton_iff, basePoint, mk_eq_mk_iff, Subtype.ext_iff, Subtype.ext_iff,
    coe_neg_sphere, coe_singleLast]
  exact (coe_toSphere_mk_eq_single_iff n v).1 (by rw [hq, coe_singleLast])

/-- The collapse map as a map of pairs `(RPⁿ, RPⁿ ∖ {[eₙ]}) ⟶ (Sⁿ, Sⁿ ∖ {eₙ})`. -/
private def toSpherePairMap :
    TopPair.ofSubset ({basePoint n}ᶜ : Set (TopCat.of (RealProjectiveSpace n))) ⟶
      TopPair.ofSubset ({toSphereChart n (basePoint n)}ᶜ : Set (TopCat.of (sphere (0 : E) 1))) :=
  TopPair.ofSubsetMap (TopCat.ofHom (toSphere n)) (mapsTo_toSphere_compl n)

variable {A : Type*} [Category A] [HasCoproducts.{0} A] [Abelian A] (R : A)

/-- **The collapse map is a local homeomorphism at `[eₙ]`**, so it induces isomorphisms
`Hₖ(RPⁿ, RPⁿ ∖ {[eₙ]}) ≅ Hₖ(Sⁿ, Sⁿ ∖ {eₙ})` on local homology. -/
private theorem isIso_singularHomologyMap_toSpherePairMap (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (toSpherePairMap n) R k) := by
  have hx := basePoint_mem_source n
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R
    (X := TopCat.of (RealProjectiveSpace n)) (toSphereChart n).open_source isClosed_singleton
    (Set.singleton_subset_iff.2 hx) k
  have hfac := singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom
    R (toSphereChart n) hx k
  rw [← TopPair.singularHomologyMap_comp] at hfac
  -- Excision onto the source followed by the collapse map is the homeomorphism of the chart
  -- followed by excision onto the target.
  have hpair : TopPair.excisionMap (X := TopCat.of (RealProjectiveSpace n))
      (toSphereChart n).source {basePoint n}ᶜ ≫ toSpherePairMap n =
      (TopPair.ofSubsetIso (X := TopCat.of (toSphereChart n).source)
        (Y := TopCat.of (toSphereChart n).target) (toSphereChart n).toHomeomorphSourceTarget
        (B := Subtype.val ⁻¹' {basePoint n}ᶜ)
        (B' := Subtype.val ⁻¹' {toSphereChart n (basePoint n)}ᶜ)
        fun z ↦ ((toSphereChart n).injOn.eq_iff z.2 hx).not.symm).hom ≫
      TopPair.excisionMap (X := TopCat.of (sphere (0 : E) 1)) (toSphereChart n).target
        {toSphereChart n (basePoint n)}ᶜ := by
    apply TopPair.hom_ext_of_fst
    ext z
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopCat.comp_app, TopCat.comp_app]
    -- The ambient spaces of these pairs are subspaces presented through `TopPair.ofSubset`, so
    -- the evaluation lemmas only match after unfolding.
    erw [TopPair.excisionMap_fst_apply, TopPair.excisionMap_fst_apply, TopPair.ofSubsetIso_hom,
      TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    rfl
  rw [← hpair, TopPair.singularHomologyMap_comp, cancel_epi] at hfac
  rw [← hfac]
  infer_instance

/-- In positive degrees `Hₖ(Sⁿ) ⟶ Hₖ(Sⁿ, Sⁿ ∖ {eₙ})` is an isomorphism, since `Sⁿ ∖ {eₙ}` is
contractible. -/
private theorem isIso_singularHomologyπ_sphere (k : ℕ) :
    IsIso ((TopPair.ofSubset ({toSphereChart n (basePoint n)}ᶜ :
      Set (TopCat.of (sphere (0 : E) 1)))).singularHomologyπ R (k + 1)) := by
  have : ContractibleSpace (TopPair.ofSubset ({toSphereChart n (basePoint n)}ᶜ :
      Set (TopCat.of (sphere (0 : E) 1)))).snd :=
    contractibleSpace_sphere_compl_singleton _
  exact TopPair.isIso_singularHomologyπ_of_contractibleSpace _ R k

section Cellular

attribute [local instance] cwComplex

variable (R : Type) [Ring R]

/-- `RPⁿ⁺¹` as the carrier of its CW structure. -/
local notation "RPCW" => (univ : Set (RealProjectiveSpace (n + 1)))

/-- The `(n + 1)`-skeleton of `RPⁿ⁺¹` is the whole space. -/
private theorem skeletonLT_eq_univ :
    (skeletonLT RPCW ((n + 1 + 1 : ℕ) : ℕ∞) :
      Set (RealProjectiveSpace (n + 1))) = univ :=
  skeletonLT_eq_complex_of_isEmpty_cell _ (n + 1 + 1) fun _ hm ↦
    ⟨fun c ↦ absurd (le_of_cell_cwComplex c) (by omega)⟩

private instance : Unique (cell RPCW (n + 1)) :=
  uniqueOfSubsingleton (Classical.choice (nonempty_cell_cwComplex le_rfl))

/-- The point `[eₙ₊₁]` of the `(n + 1)`-skeleton of `RPⁿ⁺¹`. -/
private abbrev skeletonBasePoint : skeletonObj RPCW (n + 1 + 1) :=
  ⟨basePoint (n + 1), by rw [skeletonLT_eq_univ]; exact mem_univ _⟩

private theorem skeletonBasePoint_mem_openCell :
    (skeletonBasePoint n : RealProjectiveSpace (n + 1)) ∈
      Topology.RelCWComplex.openCell (C := RPCW) (n + 1) default := by
  rw [Topology.RelCWComplex.openCell]
  -- The characteristic map is indexed by `↑(Fin.last (n + 1))`, which is `n + 1` by unfolding.
  erw [map_cwComplex (Fin.last (n + 1)), image_cellMap_ball]
  rw [mk_mem_openCell_iff]
  exact ⟨by simp, fun j hj ↦ absurd hj (not_lt.2 (Fin.le_last j))⟩

/-- In characteristic `2` every top cellular chain of `RPⁿ⁺¹` is a cycle, so
`Hₙ₊₁(Xⁿ⁺¹, ∅) ⟶ Hₙ₊₁(Xⁿ⁺¹, Xⁿ)` is an isomorphism. -/
private theorem isIso_singularHomologyMap_skeletonBasePairToSkeletonPair (h2 : (2 : R) = 0) :
    IsIso ((skeletonBasePair RPCW (n + 1)).singularHomologyMap
      (skeletonBasePairToSkeletonPair _ (n + 1)) (ModuleCat.of R R) (n + 1)) := by
  have := (cellularChainComplex RPCW (ModuleCat.of R R)).isIso_iCycles (n + 1) n (by simp)
    (cellularChainComplex_d_eq_zero_of_two_eq_zero R h2)
  have : IsIso ((skeletonBasePair RPCW (n + 1)).singularHomologyMap
      (skeletonBasePairToSkeletonPair _ (n + 1)) (ModuleCat.of R R) (n + 1) ≫
        eqToHom (cellularChainComplex_X _ (ModuleCat.of R R) (n + 1)).symm) := by
    rw [← cellularCyclesIso_inv_comp_iCycles]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (eqToHom (cellularChainComplex_X _ _ (n + 1)).symm)

/-- The chain group of the single top cell of `RPⁿ⁺¹` is the local homology at `[eₙ₊₁]`. -/
private theorem isIso_singularHomologyMap_skeletonPairToComplSingleton :
    IsIso (TopPair.singularHomologyMap (skeletonPairToComplSingleton _ (skeletonBasePoint n)
      (notMem_skeletonLT_of_mem_openCell (n + 1) (skeletonBasePoint_mem_openCell n)))
        (ModuleCat.of R R) (n + 1)) := by
  have hloc := ι_cellularChainGroupIso_inv_comp_singularHomologyMap_skeletonPairToComplSingleton
    _ (ModuleCat.of R R) (skeletonBasePoint n) (skeletonBasePoint_mem_openCell n)
  have : IsIso (Sigma.ι (fun _ : cell RPCW (n + 1) ↦ ModuleCat.of R R) default) := by
    rw [← coproductUniqueIso_inv]
    infer_instance
  rw [← Category.assoc] at hloc
  have : IsIso ((Sigma.ι (fun _ : cell RPCW (n + 1) ↦ ModuleCat.of R R) default ≫
      (cellularChainGroupIso _ (ModuleCat.of R R) (n + 1)).inv) ≫
        TopPair.singularHomologyMap (skeletonPairToComplSingleton _ (skeletonBasePoint n)
          (notMem_skeletonLT_of_mem_openCell (n + 1) (skeletonBasePoint_mem_openCell n)))
            (ModuleCat.of R R) (n + 1)) := by
    rw [hloc]
    infer_instance
  exact IsIso.of_isIso_comp_left (Sigma.ι (fun _ : cell RPCW (n + 1) ↦ ModuleCat.of R R) default ≫
    (cellularChainGroupIso _ (ModuleCat.of R R) (n + 1)).inv) _

/-- In characteristic `2`, `Hₙ₊₁(Xⁿ⁺¹) ⟶ Hₙ₊₁(Xⁿ⁺¹, Xⁿ⁺¹ ∖ {[eₙ₊₁]})` is an isomorphism for the
`(n + 1)`-skeleton `Xⁿ⁺¹` of `RPⁿ⁺¹`. -/
private theorem isIso_singularHomologyπ_skeleton (h2 : (2 : R) = 0) :
    IsIso ((TopPair.ofSubset ({skeletonBasePoint n}ᶜ :
      Set (skeletonObj RPCW (n + 1 + 1)))).singularHomologyπ (ModuleCat.of R R) (n + 1)) := by
  have hx := notMem_skeletonLT_of_mem_openCell (n + 1) (skeletonBasePoint_mem_openCell n)
  have : IsIso (TopPair.Hom.fst (skeletonBasePairToSkeletonPair RPCW (n + 1))) := by
    rw [skeletonBasePairToSkeletonPair_fst]
    exact IsIso.id _
  have : IsIso (TopPair.Hom.fst (skeletonPairToComplSingleton RPCW (skeletonBasePoint n) hx)) := by
    rw [skeletonPairToComplSingleton_fst]
    exact IsIso.id _
  have : IsIso (TopPair.Hom.fst (skeletonBasePairToSkeletonPair RPCW (n + 1) ≫
      skeletonPairToComplSingleton RPCW (skeletonBasePoint n) hx)) := by
    rw [TopPair.Hom.fst_comp]
    infer_instance
  -- The base of the skeletal base pair is empty, so its quotient map is an isomorphism.
  have : IsEmpty (skeletonBasePair RPCW (n + 1)).snd :=
    Set.isEmpty_coe_sort.2 (by simp [skeletonLT_zero_eq_base])
  have := isIso_singularHomologyMap_skeletonBasePairToSkeletonPair n R h2
  have := isIso_singularHomologyMap_skeletonPairToComplSingleton n R
  refine TopPair.isIso_singularHomologyπ_of_isIso_comp
    (skeletonBasePairToSkeletonPair RPCW (n + 1) ≫
      skeletonPairToComplSingleton RPCW (skeletonBasePoint n) hx) (ModuleCat.of R R) ?_
  rw [TopPair.singularHomologyMap_comp]
  infer_instance

/-- **The mod-2 fundamental class of `RPⁿ⁺¹`.** In characteristic `2`, the quotient map
`Hₙ₊₁(RPⁿ⁺¹) ⟶ Hₙ₊₁(RPⁿ⁺¹, RPⁿ⁺¹ ∖ {[eₙ₊₁]})` to the local homology at the centre of the top cell is
an isomorphism. -/
private theorem isIso_singularHomologyπ_complSingleton (h2 : (2 : R) = 0) :
    IsIso ((TopPair.ofSubset ({basePoint (n + 1)}ᶜ :
      Set (TopCat.of (RealProjectiveSpace (n + 1))))).singularHomologyπ
        (ModuleCat.of R R) (n + 1)) := by
  let e : skeletonObj RPCW (n + 1 + 1) ≃ₜ RealProjectiveSpace (n + 1) :=
    (Homeomorph.setCongr (skeletonLT_eq_univ n)).trans (Homeomorph.Set.univ _)
  have he (y : skeletonObj RPCW (n + 1 + 1)) :
      y ∈ ({skeletonBasePoint n}ᶜ : Set _) ↔ e y ∈ ({basePoint (n + 1)}ᶜ : Set _) :=
    not_congr ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext h⟩
  let iP := TopPair.ofSubsetIso (X := skeletonObj RPCW (n + 1 + 1))
    (Y := TopCat.of (RealProjectiveSpace (n + 1))) e he
  have : IsIso (TopPair.Hom.fst iP.hom) :=
    ⟨TopPair.Hom.fst iP.inv, by rw [← TopPair.Hom.fst_comp, iP.hom_inv_id, TopPair.Hom.fst_id],
      by rw [← TopPair.Hom.fst_comp, iP.inv_hom_id, TopPair.Hom.fst_id]⟩
  have := isIso_singularHomologyπ_skeleton n R h2
  exact TopPair.isIso_singularHomologyπ_of_isIso_comp iP.hom (ModuleCat.of R R) inferInstance

end Cellular

/-- **The collapse map `RPⁿ⁺¹ ⟶ Sⁿ⁺¹` is an isomorphism on top homology in characteristic `2`.**
For a ring `R` in which `2 = 0`, the map `Hₙ₊₁(RPⁿ⁺¹; R) ⟶ Hₙ₊₁(Sⁿ⁺¹; R)` induced by
`TauCeti.RealProjectiveSpace.toSphere` is an isomorphism. Both groups are one copy of `R`, read off
from the local homology at `[eₙ₊₁]` and at its image `eₙ₊₁`, where the collapse map is a local
homeomorphism. -/
theorem isIso_singularHomologyMap_toSphere (R : Type) [Ring R] (h2 : (2 : R) = 0) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) (n + 1)).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (toSphere (n + 1)))) := by
  have hRP := isIso_singularHomologyπ_complSingleton n R h2
  have hloc := isIso_singularHomologyMap_toSpherePairMap (n + 1) (ModuleCat.of R R) (n + 1)
  have hS := isIso_singularHomologyπ_sphere (n + 1) (ModuleCat.of R R) n
  have hfst : TopPair.Hom.fst (toSpherePairMap (n + 1)) = TopCat.ofHom (toSphere (n + 1)) :=
    TopPair.ofSubsetMap_fst _ _
  -- Read the collapse map through the local homology at `[eₙ₊₁]` and at `eₙ₊₁`.
  have hcomp : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopPair.Hom.fst (toSpherePairMap (n + 1)))) (ModuleCat.of R R) (n + 1) ≫
        (TopPair.ofSubset ({toSphereChart (n + 1) (basePoint (n + 1))}ᶜ :
          Set (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1)))).singularHomologyπ
            (ModuleCat.of R R) (n + 1)) := by
    rw [TopPair.singularHomologyπ_naturality]
    exact IsIso.comp_isIso' hRP hloc
  rw [singularHomologyFunctor_obj_map, ← hfst]
  -- The composite in `hcomp` typechecks only after unfolding `TopPair.toSSetPair_obj_right`, so
  -- instance search cannot match it and the instances are supplied as terms.
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hS hcomp

end TauCeti.RealProjectiveSpace
