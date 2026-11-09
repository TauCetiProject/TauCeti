/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Image
public import TauCeti.Analysis.Analytic.Submanifold.Product
public import TauCeti.Analysis.Analytic.Submanifold.Transport
public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import TauCeti.Geometry.RealAlgebraic.Nash.Relation
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.PartialEquiv
import Mathlib.Analysis.Analytic.Polynomial
import TauCeti.Analysis.Analytic.Constructions

/-!
# Nash maps on semialgebraic analytic submanifolds

A map `f : ℝⁿ → (τ → ℝ)` is a *Nash map* on a set `S ⊆ ℝⁿ` in dimension `d`
(`TauCeti.NashOnSubmanifold d f S`) when it is analytic on `S` in the `d`-dimensional analytic
charts of `S` (`TauCeti.AnalyticOnSubmanifold`) and its graph over `S` is semialgebraic
(`TauCeti.IsSemialgebraicOn`); in particular `S` is semialgebraic. On semialgebraic analytic
submanifolds these are the morphisms of the Nash category, read in finite affine coordinates.
They are the maps used to compare analytic simplices with semialgebraic data, for instance in
Łojasiewicz's triangulation of bounded semialgebraic sets, where the analytic open-simplex maps
also have semialgebraic graphs.

On an open set `U` the notion is the classical one: `f` is a Nash map on `U` exactly when `U` is
semialgebraic and every coordinate of `f` is a Nash germ (`TauCeti.IsNashAt`) at every point of
`U` (`IsOpen.nashOnSubmanifold_iff`). The converse direction uses that a function which is a Nash
germ along a semialgebraic set satisfies a single polynomial relation there, and the local graph
criterion. Consequently the restriction of an ambient Nash map defined on an open semialgebraic
neighbourhood of a semialgebraic analytic submanifold is a Nash map on it.

The class is closed under the operations of the category:

* restriction to open semialgebraic subsets and to smaller semialgebraic analytic submanifolds;
* polynomial maps, pointwise ring operations and polynomial postcomposition;
* pairing, and products of maps on products of submanifolds;
* composition;
* analytic left inverses: if `g` is analytic and inverts a Nash map `f` on `S`, then `g` is a Nash
  map on the analytic submanifold `f '' S`;
* chart transport along open partial homeomorphisms that are Nash maps with analytic inverses,
  such as the local Nash inverses provided by
  `TauCeti.exists_openPartialHomeomorph_of_forall_isNashAt`; their inverses are again Nash.

## Main declarations

* `TauCeti.NashOnSubmanifold d f S`: `f` is a Nash map on `S` in dimension `d`.
* `IsOpen.nashOnSubmanifold_iff`: on open sets, Nash maps are the maps with Nash coordinate germs.
* `TauCeti.nashOnSubmanifold_of_forall_isNashAt`: restrictions of ambient Nash maps.
* `TauCeti.NashOnSubmanifold.comp`: composition.
* `TauCeti.NashOnSubmanifold.prodMap`: products.
* `TauCeti.NashOnSubmanifold.of_leftInvOn`: analytic inverses of Nash maps are Nash.
* `OpenPartialHomeomorph.nashOnSubmanifold_symm`: inverses of Nash charts are Nash.
* `TauCeti.NashOnSubmanifold.comp_openPartialHomeomorph`,
  `TauCeti.NashOnSubmanifold.comp_symm_openPartialHomeomorph`: transport along Nash charts.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Sections 2.9 and 8.1 (Nash manifolds and Nash maps).
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3.
-/

public section

open Set Filter Topology MvPolynomial

namespace TauCeti

variable {n m d d' e : ℕ} {τ τ' υ : Type*} [Fintype τ] [Fintype τ'] [Fintype υ]
  {S T U : Set (Fin n → ℝ)} {f g : (Fin n → ℝ) → τ → ℝ}

/-- A map `f : ℝⁿ → (τ → ℝ)` is a *Nash map* on `S ⊆ ℝⁿ` in dimension `d` if it is analytic on
`S` in the `d`-dimensional analytic charts of `S` and its graph over `S` is semialgebraic; in
particular `S` itself is semialgebraic. Only the values of `f` on `S` matter. -/
structure NashOnSubmanifold (d : ℕ) (f : (Fin n → ℝ) → τ → ℝ) (S : Set (Fin n → ℝ)) : Prop where
  /-- A Nash map is analytic in the analytic charts of its domain. -/
  analyticOnSubmanifold : AnalyticOnSubmanifold d f S
  /-- A Nash map has a semialgebraic graph over its semialgebraic domain. -/
  isSemialgebraicOn : IsSemialgebraicOn f S

/-- Unfolding `TauCeti.NashOnSubmanifold`. -/
theorem nashOnSubmanifold_iff :
    NashOnSubmanifold d f S ↔ AnalyticOnSubmanifold d f S ∧ IsSemialgebraicOn f S :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace NashOnSubmanifold

/-- The domain of a Nash map is semialgebraic. -/
theorem isSemialgebraic (hf : NashOnSubmanifold d f S) : IsSemialgebraic S :=
  hf.isSemialgebraicOn.isSemialgebraic

/-- A Nash map is continuous on its domain. -/
theorem continuousOn (hf : NashOnSubmanifold d f S) : ContinuousOn f S :=
  hf.analyticOnSubmanifold.continuousOn

/-- Being a Nash map on `S` only depends on the values on `S`. -/
theorem congr (hf : NashOnSubmanifold d f S) (hfg : EqOn f g S) : NashOnSubmanifold d g S :=
  ⟨hf.analyticOnSubmanifold.congr hfg, hf.isSemialgebraicOn.congr hfg⟩

/-! ### Restriction -/

/-- A Nash map restricts to the intersection of its domain with an open semialgebraic set. -/
theorem inter (hf : NashOnSubmanifold d f S) (hU : IsOpen U) (hU' : IsSemialgebraic U) :
    NashOnSubmanifold d f (S ∩ U) :=
  ⟨hf.analyticOnSubmanifold.inter hU,
    hf.isSemialgebraicOn.mono (hf.isSemialgebraic.inter hU') inter_subset_left⟩

/-- A Nash map restricts to a semialgebraic analytic submanifold of its domain, possibly of
smaller dimension. -/
theorem mono (hf : NashOnSubmanifold d f S) (hTS : T ⊆ S) (hT : IsAnalyticSubmanifold d' T)
    (hT' : IsSemialgebraic T) : NashOnSubmanifold d' f T :=
  ⟨hf.analyticOnSubmanifold.mono hTS hT, hf.isSemialgebraicOn.mono hT' hTS⟩

end NashOnSubmanifold

/-- Being a Nash map on `S` only depends on the values on `S`. -/
theorem nashOnSubmanifold_congr (hfg : EqOn f g S) :
    NashOnSubmanifold d f S ↔ NashOnSubmanifold d g S :=
  ⟨fun hf ↦ hf.congr hfg, fun hg ↦ hg.congr hfg.symm⟩

/-! ### Nash maps on open sets and restrictions of ambient Nash maps -/

/-- On an open subset `U` of `ℝⁿ`, a map is a Nash map in dimension `n` exactly when `U` is
semialgebraic and every coordinate of the map is a Nash germ at every point of `U`. -/
theorem _root_.IsOpen.nashOnSubmanifold_iff (hU : IsOpen U) :
    NashOnSubmanifold n f U ↔ IsSemialgebraic U ∧ ∀ x ∈ U, ∀ i, IsNashAt (fun y ↦ f y i) x := by
  constructor
  · intro hf
    have ha := hf.analyticOnSubmanifold.analyticOnNhd_of_isOpen hU
    refine ⟨hf.isSemialgebraic, fun x hx i ↦ ?_⟩
    exact ((isSemialgebraicOn_pi_iff.1 hf.isSemialgebraicOn).2 i).isNashAt
      (analyticAt_pi_iff.1 (ha x hx) i) (hU.mem_nhds hx)
  · rintro ⟨hU', hf⟩
    refine ⟨hU.analyticOnSubmanifold_iff.2 fun x hx ↦
      analyticAt_pi_iff.2 fun i ↦ (hf x hx i).analyticAt, .pi hU' fun i ↦ ?_⟩
    -- Each coordinate satisfies one polynomial relation on all of `U`, and the graph criterion
    -- makes its graph semialgebraic.
    obtain ⟨P, hP, hrel⟩ :=
      hU'.exists_ne_zero_polynomial_relation_of_isNashAt fun x hx ↦ hf x hx i
    exact isSemialgebraicOn_of_polynomial_relation hU' hU
      (fun x hx ↦ (hf x hx i).analyticAt.continuousAt.continuousWithinAt) P hP
      fun x hx ↦ Polynomial.IsRoot.def.2 (hrel x hx)

/-- **Restriction of ambient Nash maps.** A map whose coordinates are Nash germs at every point of
an open semialgebraic neighbourhood `U` of a semialgebraic analytic submanifold `S` is a Nash map
on `S`. -/
theorem nashOnSubmanifold_of_forall_isNashAt (hU : IsOpen U) (hU' : IsSemialgebraic U)
    (hf : ∀ x ∈ U, ∀ i, IsNashAt (fun y ↦ f y i) x) (hSU : S ⊆ U)
    (hS : IsAnalyticSubmanifold d S) (hS' : IsSemialgebraic S) : NashOnSubmanifold d f S :=
  (hU.nashOnSubmanifold_iff.2 ⟨hU', hf⟩).mono hSU hS hS'

/-! ### Polynomial maps -/

/-- Polynomial maps are Nash maps on every semialgebraic analytic submanifold. -/
theorem nashOnSubmanifold_eval (p : τ → MvPolynomial (Fin n) ℝ) (hS : IsAnalyticSubmanifold d S)
    (hS' : IsSemialgebraic S) : NashOnSubmanifold d (fun x i ↦ eval x (p i)) S :=
  ⟨(analyticOnNhd_pi_iff.2 fun i ↦ (AnalyticOnNhd.eval_mvPolynomial (p i)).mono
      (subset_univ S)).analyticOnSubmanifold hS,
    isSemialgebraicOn_eval p hS'⟩

/-- Constant maps are Nash maps on every semialgebraic analytic submanifold. -/
theorem nashOnSubmanifold_const (c : τ → ℝ) (hS : IsAnalyticSubmanifold d S)
    (hS' : IsSemialgebraic S) : NashOnSubmanifold d (fun _ ↦ c) S := by
  simpa using nashOnSubmanifold_eval (fun i ↦ C (c i)) hS hS'

/-- The identity is a Nash map on every semialgebraic analytic submanifold. -/
theorem nashOnSubmanifold_id (hS : IsAnalyticSubmanifold d S) (hS' : IsSemialgebraic S) :
    NashOnSubmanifold d id S :=
  (nashOnSubmanifold_eval (fun i ↦ X i) hS hS').congr fun _ _ ↦ by ext; simp

namespace NashOnSubmanifold

/-! ### Algebraic operations -/

/-- Applying a polynomial map to the values of a Nash map gives a Nash map. -/
theorem eval_comp (hf : NashOnSubmanifold d f S) (p : υ → MvPolynomial τ ℝ) :
    NashOnSubmanifold d (fun x i ↦ eval (f x) (p i)) S :=
  ⟨(analyticOnNhd_pi_iff.2 fun i ↦ AnalyticOnNhd.eval_mvPolynomial (p i)).comp_analyticOnSubmanifold
      hf.analyticOnSubmanifold (mapsTo_univ _ _),
    hf.isSemialgebraicOn.eval_comp p⟩

/-- The pointwise sum of Nash maps is a Nash map. -/
theorem add (hf : NashOnSubmanifold d f S) (hg : NashOnSubmanifold d g S) :
    NashOnSubmanifold d (f + g) S :=
  ⟨AnalyticOnNhd.comp_analyticOnSubmanifold (g := fun p : (τ → ℝ) × (τ → ℝ) ↦ p.1 + p.2)
      (fun _ _ ↦ analyticAt_fst.add analyticAt_snd)
      (hf.analyticOnSubmanifold.prod hg.analyticOnSubmanifold) (mapsTo_univ _ _),
    hf.isSemialgebraicOn.add hg.isSemialgebraicOn⟩

/-- The pointwise negation of a Nash map is a Nash map. -/
theorem neg (hf : NashOnSubmanifold d f S) : NashOnSubmanifold d (-f) S :=
  ⟨AnalyticOnNhd.comp_analyticOnSubmanifold (g := fun y : τ → ℝ ↦ -y)
      (fun _ _ ↦ analyticAt_id.neg) hf.analyticOnSubmanifold (mapsTo_univ _ _),
    hf.isSemialgebraicOn.neg⟩

/-- The pointwise difference of Nash maps is a Nash map. -/
theorem sub (hf : NashOnSubmanifold d f S) (hg : NashOnSubmanifold d g S) :
    NashOnSubmanifold d (f - g) S := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- The pointwise product of Nash maps is a Nash map. -/
theorem mul (hf : NashOnSubmanifold d f S) (hg : NashOnSubmanifold d g S) :
    NashOnSubmanifold d (f * g) S :=
  ⟨AnalyticOnNhd.comp_analyticOnSubmanifold (g := fun p : (τ → ℝ) × (τ → ℝ) ↦ p.1 * p.2)
      (fun _ _ ↦ analyticAt_fst.mul analyticAt_snd)
      (hf.analyticOnSubmanifold.prod hg.analyticOnSubmanifold) (mapsTo_univ _ _),
    hf.isSemialgebraicOn.mul hg.isSemialgebraicOn⟩

/-! ### Pairs and products -/

/-- The pair of two Nash maps on the same domain, with values in the disjoint union of their
coordinates, is a Nash map. -/
theorem sumElim {g : (Fin n → ℝ) → τ' → ℝ} (hf : NashOnSubmanifold d f S)
    (hg : NashOnSubmanifold d g S) : NashOnSubmanifold d (fun x ↦ Sum.elim (f x) (g x)) S :=
  ⟨analyticOnNhd_sumElim.comp_analyticOnSubmanifold
      (hf.analyticOnSubmanifold.prod hg.analyticOnSubmanifold) (mapsTo_univ _ _),
    hf.isSemialgebraicOn.sumElim hg.isSemialgebraicOn⟩

/-- **Products.** Nash maps on two semialgebraic sets combine into a Nash map on their product,
represented in `ℝⁿ⁺ᵐ` by concatenating coordinates, with the values of the two maps placed in the
disjoint union of their coordinates. Only dimension bounds are needed. -/
theorem prodMap {T : Set (Fin m → ℝ)} {g : (Fin m → ℝ) → τ' → ℝ} (hf : NashOnSubmanifold d f S)
    (hg : NashOnSubmanifold e g T) (hd : d ≤ n) (he : e ≤ m) :
    NashOnSubmanifold (d + e)
      (fun x : Fin (n + m) → ℝ ↦
        Sum.elim (f fun i ↦ x (Fin.castAdd m i)) (g fun i ↦ x (Fin.natAdd n i)))
      {x | (fun i ↦ x (Fin.castAdd m i)) ∈ S ∧ (fun i ↦ x (Fin.natAdd n i)) ∈ T} := by
  set P : Set (Fin (n + m) → ℝ) :=
    {x | (fun i ↦ x (Fin.castAdd m i)) ∈ S ∧ (fun i ↦ x (Fin.natAdd n i)) ∈ T}
  have hP : IsSemialgebraic P :=
    (hf.isSemialgebraic.preimage_comp (Fin.castAdd m)).inter
      (hg.isSemialgebraic.preimage_comp (Fin.natAdd n))
  -- Each factor, read through the coordinate projection of its block, is semialgebraic on `P`.
  have hl : IsSemialgebraicOn (fun x : Fin (n + m) → ℝ ↦ f fun i ↦ x (Fin.castAdd m i)) P := by
    simpa [Function.comp_def] using (hf.isSemialgebraicOn.comp_eval
      fun i ↦ X (Fin.castAdd m i)).mono hP fun x hx ↦ by simpa using hx.1
  have hr : IsSemialgebraicOn (fun x : Fin (n + m) → ℝ ↦ g fun i ↦ x (Fin.natAdd n i)) P := by
    simpa [Function.comp_def] using (hg.isSemialgebraicOn.comp_eval
      fun i ↦ X (Fin.natAdd n i)).mono hP fun x hx ↦ by simpa using hx.2
  exact ⟨analyticOnNhd_sumElim.comp_analyticOnSubmanifold
      (hf.analyticOnSubmanifold.prodMap hg.analyticOnSubmanifold hd he) (mapsTo_univ _ _),
    hl.sumElim hr⟩

end NashOnSubmanifold

/-- A pair of maps is a Nash map exactly when both of its components are. -/
@[simp]
theorem nashOnSubmanifold_sumElim_iff {g : (Fin n → ℝ) → τ' → ℝ} :
    NashOnSubmanifold d (fun x ↦ Sum.elim (f x) (g x)) S ↔
      NashOnSubmanifold d f S ∧ NashOnSubmanifold d g S := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.sumElim h.2⟩
  · simpa using h.eval_comp fun i : τ ↦ X (Sum.inl i)
  · simpa using h.eval_comp fun i : τ' ↦ X (Sum.inr i)

namespace NashOnSubmanifold

/-! ### Composition -/

/-- **Composition.** If `f` is a Nash map on `S` with values in `T`, and `g` is a Nash map on `T`,
then `g ∘ f` is a Nash map on `S`. -/
theorem comp {T : Set (Fin m → ℝ)} {g : (Fin m → ℝ) → υ → ℝ} {f : (Fin n → ℝ) → Fin m → ℝ}
    (hg : NashOnSubmanifold d' g T) (hf : NashOnSubmanifold d f S) (h : MapsTo f S T) :
    NashOnSubmanifold d (g ∘ f) S :=
  ⟨hg.analyticOnSubmanifold.comp hf.analyticOnSubmanifold h,
    hg.isSemialgebraicOn.comp hf.isSemialgebraicOn h⟩

/-! ### Inverses -/

/-- **Nash inverses.** Let `f` be a Nash map on a `d`-dimensional analytic submanifold `S` with
values in `T`, and let `g` be analytic on `T` with `g ∘ f = id` on `S`. Then `g` is a Nash map on
`f '' S`, in dimension `d`. The image `f '' S` is itself a `d`-dimensional analytic submanifold
by `TauCeti.IsAnalyticSubmanifold.image_of_leftInvOn`. -/
theorem of_leftInvOn {T : Set (Fin m → ℝ)} {f : (Fin n → ℝ) → Fin m → ℝ}
    {g : (Fin m → ℝ) → Fin n → ℝ} (hf : NashOnSubmanifold d f S) (hS : IsAnalyticSubmanifold d S)
    (hg : AnalyticOnSubmanifold d' g T) (hfT : MapsTo f S T) (hgf : LeftInvOn g f S) :
    NashOnSubmanifold d g (f '' S) := by
  refine ⟨hg.mono (image_subset_iff.2 hfT)
    (hS.image_of_leftInvOn hf.analyticOnSubmanifold hg hfT hgf), ?_⟩
  -- `f` and `g` form a partial equivalence between `S` and `f '' S`, whose inverse has the
  -- exchanged graph.
  let φ : PartialEquiv (Fin n → ℝ) (Fin m → ℝ) :=
    { toFun := f
      invFun := g
      source := S
      target := f '' S
      map_source' := mapsTo_image f S
      map_target' := by
        rintro _ ⟨x, hx, rfl⟩
        rwa [hgf hx]
      left_inv' := hgf
      right_inv' := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hgf hx] }
  exact φ.isSemialgebraicOn_symm hf.isSemialgebraicOn

/-! ### Transport along Nash charts -/

variable {n' : ℕ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n' → ℝ)}

/-- The inverse of an open partial homeomorphism whose graph over its source is semialgebraic,
and whose inverse is analytic, is a Nash map on its target. In particular this applies to Nash
maps on their source with analytic inverse. -/
theorem _root_.OpenPartialHomeomorph.nashOnSubmanifold_symm
    (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n' → ℝ)) (hφ : IsSemialgebraicOn φ φ.source)
    (hφs : AnalyticOnNhd ℝ φ.symm φ.target) : NashOnSubmanifold n' φ.symm φ.target :=
  ⟨φ.open_target.analyticOnSubmanifold_iff.2 hφs, φ.toPartialEquiv.isSemialgebraicOn_symm hφ⟩

/-- **Chart transport.** Precomposing a Nash map on `T` with an open partial homeomorphism `φ`
which is a Nash map on its source with analytic inverse gives a Nash map on `S`, when
`S ⊆ φ.source` and `φ` maps `S` onto the part of `T` in its target. -/
theorem comp_openPartialHomeomorph {T : Set (Fin n' → ℝ)} {f : (Fin n' → ℝ) → τ → ℝ}
    (hf : NashOnSubmanifold d f T) (hφ : NashOnSubmanifold n φ φ.source)
    (hφs : AnalyticOnNhd ℝ φ.symm φ.target) (hS : S ⊆ φ.source) (hST : φ.IsImage S T) :
    NashOnSubmanifold d (f ∘ φ) S := by
  have hφT : MapsTo φ S T := fun _ hx ↦ (hST (hS hx)).2 hx
  have hS' : S = φ.source ∩ φ ⁻¹' T :=
    Subset.antisymm (fun x hx ↦ ⟨hS hx, hφT hx⟩) fun x hx ↦ (hST hx.1).1 hx.2
  have hSs : IsSemialgebraic S := hS' ▸ hφ.isSemialgebraicOn.isSemialgebraic_inter_preimage
    hf.isSemialgebraic
  exact ⟨hf.analyticOnSubmanifold.comp_openPartialHomeomorph
      (hφ.analyticOnSubmanifold.analyticOnNhd_of_isOpen φ.open_source) hφs hS hST,
    hf.isSemialgebraicOn.comp (hφ.isSemialgebraicOn.mono hSs hS) hφT⟩

/-- **Chart transport.** Pushing a Nash map on `S` forward along an open partial homeomorphism
`φ` which is a Nash map on its source with analytic inverse gives a Nash map on
`φ '' (S ∩ φ.source)`. -/
theorem comp_symm_openPartialHomeomorph (hf : NashOnSubmanifold d f S)
    (hφ : NashOnSubmanifold n φ φ.source) (hφs : AnalyticOnNhd ℝ φ.symm φ.target) :
    NashOnSubmanifold d (f ∘ φ.symm) (φ '' (S ∩ φ.source)) := by
  refine hf.comp_openPartialHomeomorph (φ := φ.symm)
    (φ.nashOnSubmanifold_symm hφ.isSemialgebraicOn hφs)
    (hφ.analyticOnSubmanifold.analyticOnNhd_of_isOpen φ.open_source) ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact φ.map_source hx
  · refine ⟨fun hyS ↦ ⟨φ.symm y, ⟨hyS, φ.map_target hy⟩, φ.right_inv hy⟩, ?_⟩
    rintro ⟨x, ⟨hxS, hx⟩, rfl⟩
    rwa [φ.left_inv hx]

end NashOnSubmanifold

end TauCeti
