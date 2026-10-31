/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.RCLike.Lemmas
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.LinearAlgebra.Projectivization.Basic
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The quotient topology on projective space

`ℙ K V` is the quotient of the nonzero vectors `{v : V // v ≠ 0}` by the action of `Kˣ`.
When `V` carries a topology we give `ℙ K V` the quotient topology, and we show that the
quotient map `Projectivization.mk'` is an open quotient map as soon as scalar multiplication
by units of `K` is continuous on `V`.

We then prove the separation and compactness properties of this topology which make
projective space a compact Hausdorff space, the ambient space of projective algebraic sets.
Over a topological field `K` whose continuous linear forms on `V` separate points (for instance
any normed space over `ℝ` or `ℂ`, by the Hahn–Banach theorem), two nonzero vectors span the same
line exactly when `f v * g w = f w * g v` for all continuous linear forms `f` and `g`. These are
closed conditions, so the relation is closed and `ℙ K V` is Hausdorff. Over `ℝ` or `ℂ` every
line meets the unit sphere, so for finite-dimensional `V` the projective space is a continuous
image of a compact sphere and is compact. Second countability passes to `ℙ K V` along the open
quotient map.

Finally, over a field with continuous multiplication and inversion, the standard affine charts
`Projectivization.affineChart i` of `ℙ K (Fin (n + 1) → K)` are homeomorphisms from the open sets
`U_i = {[v] | v i ≠ 0}` onto the affine space `Fin n → K`. These charts form the standard atlas
of projective space.

## Main results

* `Projectivization.instTopologicalSpace`: the quotient topology on `ℙ K V`.
* `Projectivization.isQuotientMap_mk'`, `Projectivization.continuous_mk'`:
  `mk' K : {v : V // v ≠ 0} → ℙ K V` is a quotient map, in particular continuous.
* `Projectivization.isOpenQuotientMap_mk'`: `mk' K` is an open quotient map when `Kˣ` acts
  continuously on `V`.
* `Projectivization.continuous_iff`: a map out of `ℙ K V` is continuous iff its composite with
  `mk' K` is.
* `Projectivization.continuous_mk`, `Projectivization.continuous_map`: `Projectivization.mk`
  and `Projectivization.map` are continuous.
* `Projectivization.mk'_eq_mk'_iff_forall_strongDual`: when continuous linear forms separate
  points, two nonzero vectors span the same line iff all the `2 × 2` minors
  `f v * g w - f w * g v` vanish.
* `Projectivization.instT2Space`: `ℙ K V` is Hausdorff when continuous linear forms separate
  points.
* `Projectivization.instCompactSpace`: `ℙ 𝕜 V` is compact for a finite-dimensional normed space
  `V` over `ℝ` or `ℂ`.
* `Projectivization.instSecondCountableTopology`: `ℙ K V` is second countable when `V` is.
* `Projectivization.isOpen_affineOpen`: the standard affine opens are open.
* `Projectivization.affineOpenPartialHomeomorph`: the standard affine chart as an open partial
  homeomorphism from `U_i` onto `Fin n → K`.

The topology and its quotient-map API (`instTopologicalSpace` through `isOpenQuotientMap_mk'`)
follow Zayn Blore's Mathlib pull request
[mathlib4#44117](https://github.com/leanprover-community/mathlib4/pull/44117), with the same names
and statements.
-/

public section

open Set Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

section Topology

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

variable [TopologicalSpace V]

/-- The quotient topology on `ℙ K V`, coinduced by `Projectivization.mk'`. -/
instance instTopologicalSpace : TopologicalSpace (ℙ K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))

/-- The map `mk' K` from nonzero vectors to `ℙ K V` is a quotient map. -/
theorem isQuotientMap_mk' : IsQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  isQuotientMap_quotient_mk'

/-- The map `mk' K` from nonzero vectors to `ℙ K V` is continuous. -/
@[fun_prop]
theorem continuous_mk' : Continuous (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_quotient_mk'

variable {α : Type*} [TopologicalSpace α]

/-- A map out of `ℙ K V` is continuous iff its composite with `mk' K` is continuous. -/
theorem continuous_iff {f : ℙ K V → α} : Continuous f ↔ Continuous (f ∘ mk' K) :=
  isQuotientMap_mk'.continuous_iff

/-- `Projectivization.mk` is continuous in the vector, as long as the vector stays nonzero. -/
@[fun_prop]
theorem continuous_mk {f : α → V} (hf : Continuous f) (hf₀ : ∀ x, f x ≠ 0) :
    Continuous fun x ↦ mk K (f x) (hf₀ x) :=
  continuous_mk'.comp (hf.subtype_mk hf₀)

section Map

variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W] [TopologicalSpace W]

/-- An injective continuous semilinear map induces a continuous map on projective spaces. -/
theorem continuous_map {σ : K →+* L} {f : V →ₛₗ[σ] W} (hf : Function.Injective f)
    (hfc : Continuous f) : Continuous (map f hf) :=
  continuous_iff.2 <| continuous_mk (hfc.comp continuous_subtype_val) _

end Map

variable [ContinuousConstSMul Kˣ V]

/-- When scalar multiplication by units of `K` is continuous on `V`, the map `mk' K` from
nonzero vectors to `ℙ K V` is open. -/
theorem isOpenMap_mk' : IsOpenMap (mk' K : {v : V // v ≠ 0} → ℙ K V) := fun U hU ↦ by
  rw [← isQuotientMap_mk'.isOpen_preimage, preimage_image_mk']
  exact isOpen_iUnion fun a ↦ isOpenMap_smul a U hU

/-- When scalar multiplication by units of `K` is continuous on `V`, the map `mk' K` from
nonzero vectors to `ℙ K V` is an open quotient map. -/
theorem isOpenQuotientMap_mk' : IsOpenQuotientMap (mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  ⟨Quotient.mk''_surjective, continuous_mk', isOpenMap_mk'⟩

/-- Projective space is second countable when the vector space is. -/
instance instSecondCountableTopology [SecondCountableTopology V] :
    SecondCountableTopology (ℙ K V) :=
  have : SecondCountableTopology {v : V // v ≠ 0} :=
    TopologicalSpace.secondCountableTopology_induced _ V Subtype.val
  isOpenQuotientMap_mk'.secondCountableTopology

end Topology

section Field

variable {K V : Type*} [Field K] [TopologicalSpace K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V]

/-- When continuous linear forms separate the points of `V`, two nonzero vectors span the same
line iff the `2 × 2` minors `f v * g w - f w * g v` vanish for all continuous linear forms `f`
and `g`. -/
theorem mk'_eq_mk'_iff_forall_strongDual [SeparatingDual K V] (v w : {v : V // v ≠ 0}) :
    mk' K v = mk' K w ↔ ∀ f g : StrongDual K V, f v * g w = f w * g v := by
  rw [mk'_eq_mk'_iff]
  constructor
  · rintro ⟨a, rfl⟩ f g
    simp only [Units.smul_coe, Units.smul_def, map_smul, smul_eq_mul]
    ring
  · intro h
    obtain ⟨f, hf⟩ := SeparatingDual.exists_ne_zero (R := K) w.2
    -- A form `f` not vanishing on `w` determines the ratio `c = f v / f w` with `v = c • w`.
    have hvw : (v : V) = (f v / f w) • (w : V) := by
      rw [← sub_eq_zero]
      refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := K) fun g ↦ ?_
      rw [map_sub, map_smul, smul_eq_mul]
      field_simp
      linear_combination -h f g
    have hc : f v / f w ≠ 0 := fun hc ↦ v.2 (by rw [hvw, hc, zero_smul])
    exact ⟨Units.mk0 _ hc, Subtype.ext (by rw [Units.smul_coe, Units.smul_def,
      Units.val_mk0, ← hvw])⟩

/-- **Projective space is Hausdorff** over a Hausdorff topological field, when continuous linear
forms separate the points of `V`: the relation of spanning the same line is cut out by the closed
conditions `f v * g w = f w * g v`, and the quotient map is open. -/
instance instT2Space [T2Space K] [ContinuousMul K] [ContinuousConstSMul Kˣ V]
    [SeparatingDual K V] : T2Space (ℙ K V) := by
  rw [t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_mk']
  have hrel : {q : {v : V // v ≠ 0} × {v : V // v ≠ 0} | mk' K q.1 = mk' K q.2} =
      ⋂ (f : StrongDual K V) (g : StrongDual K V),
        {q | f q.1 * g q.2 = f q.2 * g q.1} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter, mk'_eq_mk'_iff_forall_strongDual]
  rw [hrel]
  exact isClosed_iInter fun f ↦ isClosed_iInter fun g ↦ isClosed_eq (by fun_prop) (by fun_prop)

end Field

section RCLike

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Every point of `ℙ 𝕜 V` is spanned by a unit vector. -/
theorem exists_norm_eq_one_mk_eq (x : ℙ 𝕜 V) :
    ∃ (v : V) (hv : v ≠ 0), ‖v‖ = 1 ∧ mk 𝕜 v hv = x := by
  refine ⟨(‖x.rep‖⁻¹ : 𝕜) • x.rep, smul_ne_zero (by simpa using x.rep_nonzero) x.rep_nonzero,
    norm_smul_inv_norm x.rep_nonzero, ?_⟩
  conv_rhs => rw [← x.mk_rep]
  exact (mk_eq_mk_iff' 𝕜 _ _ _ x.rep_nonzero).2 ⟨_, rfl⟩

/-- **Projective space is compact** for a finite-dimensional normed space over `ℝ` or `ℂ`: it is
the image of the compact unit sphere. -/
instance instCompactSpace [FiniteDimensional 𝕜 V] : CompactSpace (ℙ 𝕜 V) := by
  have := FiniteDimensional.proper_rclike 𝕜 V
  have : CompactSpace (Metric.sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  refine Function.Surjective.compactSpace (f := fun v : Metric.sphere (0 : V) 1 ↦
    mk 𝕜 (v : V) (ne_zero_of_mem_sphere one_ne_zero v))
    (continuous_mk continuous_subtype_val _) fun x ↦ ?_
  obtain ⟨v, -, hv, rfl⟩ := exists_norm_eq_one_mk_eq x
  exact ⟨⟨v, mem_sphere_zero_iff_norm.2 hv⟩, rfl⟩

end RCLike

/-! ### The standard affine charts -/

section AffineOpen

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [T1Space K] {ι : Type*}

/-- The standard affine open of projective space, where a given homogeneous coordinate is
nonzero, is open. -/
theorem isOpen_affineOpen (i : ι) : IsOpen (affineOpen (K := K) i) := by
  rw [← isQuotientMap_mk'.isOpen_preimage]
  have : mk' K ⁻¹' affineOpen i = (fun v : {v : ι → K // v ≠ 0} ↦ v.1 i) ⁻¹' {0}ᶜ := by
    ext v
    simp [mk'_eq_mk]
  rw [this]
  exact isOpen_compl_singleton.preimage ((continuous_apply i).comp continuous_subtype_val)

end AffineOpen

section AffineChart

variable {K : Type*} [Field K] [TopologicalSpace K] {n : ℕ}

/-- The inverse `z ↦ [Fin.insertNth i 1 z]` of the standard affine chart is continuous. -/
theorem continuous_affineChart_symm (i : Fin (n + 1)) :
    Continuous (affineChart (K := K) i).symm := by
  rw [funext (affineChart_symm_apply i)]
  exact continuous_mk ((continuous_const (y := (1 : K))).finInsertNth (A := fun _ ↦ K) i
    continuous_id) _

variable [ContinuousMul K] [ContinuousInv₀ K] [T1Space K]

/-- The standard affine chart of projective space is continuous on its domain. -/
theorem continuousOn_affineChart (i : Fin (n + 1)) :
    ContinuousOn (affineChart (K := K) i) (affineOpen i) := by
  refine (isOpen_affineOpen i).continuousOn_iff.2 fun x hx ↦ ?_
  obtain ⟨v, rfl⟩ := isOpenQuotientMap_mk'.surjective x
  rw [mk'_eq_mk, mk_mem_affineOpen_iff] at hx
  -- Composed with the quotient map, the chart is a family of ratios of coordinates.
  have hchart : affineChart i ∘ mk' K = fun v : {v : Fin (n + 1) → K // v ≠ 0} ↦
      fun j ↦ v.1 (i.succAbove j) / v.1 i :=
    funext fun v ↦ affineChart_mk i v.1 v.2
  have hcoord (j : Fin (n + 1)) : Continuous fun v : {v : Fin (n + 1) → K // v ≠ 0} ↦ v.1 j :=
    (continuous_apply j).comp continuous_subtype_val
  rw [← isOpenQuotientMap_mk'.continuousAt_comp_iff, hchart]
  exact continuousAt_pi.2 fun j ↦ (hcoord _).continuousAt.div₀ (hcoord i).continuousAt hx

/-- The standard affine chart of projective space at the coordinate `i`, as an open partial
homeomorphism from the affine open `U_i = {[v] | v i ≠ 0}` onto `Fin n → K`. -/
noncomputable def affineOpenPartialHomeomorph (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ℙ K (Fin (n + 1) → K)) (Fin n → K) where
  toPartialEquiv := affineChart i
  open_source := by simpa using isOpen_affineOpen i
  open_target := by simp
  continuousOn_toFun := by simpa using continuousOn_affineChart i
  continuousOn_invFun := (continuous_affineChart_symm i).continuousOn

@[simp]
theorem affineOpenPartialHomeomorph_toPartialEquiv (i : Fin (n + 1)) :
    (affineOpenPartialHomeomorph (K := K) i).toPartialEquiv = affineChart i :=
  (rfl)

@[simp]
theorem coe_affineOpenPartialHomeomorph (i : Fin (n + 1)) :
    ⇑(affineOpenPartialHomeomorph (K := K) i) = affineChart i :=
  (rfl)

@[simp]
theorem coe_affineOpenPartialHomeomorph_symm (i : Fin (n + 1)) :
    ⇑(affineOpenPartialHomeomorph (K := K) i).symm = (affineChart i).symm :=
  (rfl)

end AffineChart

end Projectivization
