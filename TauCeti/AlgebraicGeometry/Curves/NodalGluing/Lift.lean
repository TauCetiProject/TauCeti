/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Iso
public import TauCeti.Topology.Connected.Basic
public import Mathlib.Topology.ExtendFrom

/-!
# Lifting homeomorphisms of glued nodal curves to the normalizations

A homeomorphism of glued curves `h : GluedCurve d ≃ₜ GluedCurve d'` which maps nodes exactly to
nodes lifts to a unique homeomorphism of the normalizations `(Σ i, X i) ≃ₜ (Σ i, X' i)` covering
it. Away from the flag points the lift is forced, because there the quotient maps are open
embeddings. At a flag point `p` the lift has to choose one of the two branch points over the
image under `h` of the node of `p`. This choice is made by connectedness: if the punctured
neighbourhoods of `p` are connected, then near `p` the punctured neighbourhood is carried into a
small neighbourhood of a single branch point, and the lift sends `p` to that branch point.

The connectedness hypothesis is that every flag point `x` has arbitrarily small neighbourhoods
`V` with `V \ {x}` connected. It holds on manifolds modelled on a real normed space of dimension
greater than one, by `TauCeti.exists_mem_nhds_subset_isConnected_sdiff_singleton`, and so for
complex curves. It fails for real one-dimensional components, where a homeomorphism of the glued
space may exchange the half-branches of different branches.

## Main definitions

* `NodalGluing.liftHomeomorph`: the homeomorphism of normalizations covering a node-preserving
  homeomorphism of glued curves.
* `NodalGluing.Iso.ofGluedCurveHomeomorph`: the isomorphism of nodal curves whose underlying
  map is that lift, when the lift and its inverse are `C^n`.

## Main results

* `NodalGluing.mk_liftHomeomorph`: the lift covers `h`.
* `NodalGluing.eq_liftHomeomorph`: it is the only continuous map covering `h`.
* `NodalGluing.flagRel_liftHomeomorph_iff`: it carries flag pairs exactly to flag pairs.
* `NodalGluing.Iso.liftHomeomorph_gluedCurveHomeomorph`: lifting the descent of an isomorphism
  recovers the isomorphism, and `NodalGluing.Iso.gluedCurveHomeomorph_ofGluedCurveHomeomorph`:
  descending the lift recovers `h`. So, under the connectedness hypothesis above, descent is a
  bijection between isomorphisms of nodal curves and node-preserving homeomorphisms of glued
  curves whose lifts are `C^n` in both directions.

For complex curves the lift of a homeomorphism which is holomorphic away from the nodes is
holomorphic at the flag points as well, by Riemann's removable singularity theorem; that
statement is not part of this file.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699: an isomorphism of nodal Riemann surfaces is a
  biholomorphism of the normalizations carrying nodal pairs to nodal pairs.
* Enrico Arbarello, Maurizio Cornalba, Phillip A. Griffiths, *Geometry of Algebraic Curves,
  Volume II*, Chapter X, for the normalization of a nodal curve.
-/

public noncomputable section

open Filter Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

variable {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  {ι' Flag' : Type*} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)]
  {d : FlagPairData ι Flag X} {d' : FlagPairData ι' Flag' X'}

/-- A choice of a point over the image of `x`; away from the flag points this is the only one. -/
private def liftAux (h : GluedCurve d ≃ₜ GluedCurve d') (x : Σ i, X i) : Σ i, X' i :=
  (h (Quotient.mk (gluedRelSetoid d) x)).out

private theorem mk_liftAux (h : GluedCurve d ≃ₜ GluedCurve d') (x : Σ i, X i) :
    Quotient.mk (gluedRelSetoid d') (liftAux h x) = h (Quotient.mk (gluedRelSetoid d) x) :=
  Quotient.out_eq _

/-- A point covering the image of `x` is a flag point exactly when `x` is one. -/
private theorem mem_flagPointSet_iff_of_mk_eq {h : GluedCurve d ≃ₜ GluedCurve d'}
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d) {x : Σ i, X i} {y : Σ i, X' i}
    (hy : Quotient.mk (gluedRelSetoid d') y = h (Quotient.mk (gluedRelSetoid d) x)) :
    y ∈ flagPointSet d' ↔ x ∈ flagPointSet d := by
  rw [← preimage_nodeSet d', ← preimage_nodeSet d, mem_preimage, mem_preimage, hy, hN]

variable [∀ i, T2Space (X' i)]

/-- Two continuous maps covering the same map of glued curves, which sends no point outside the
node set into it, agree. -/
private theorem eq_of_mk_eq_mk {k : GluedCurve d → GluedCurve d'}
    (hk : ∀ z, k z ∈ nodeSet d' → z ∈ nodeSet d) (hd : Dense (flagPointSet d)ᶜ)
    {g₁ g₂ : (Σ i, X i) → Σ i, X' i} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (h₁ : ∀ x, Quotient.mk (gluedRelSetoid d') (g₁ x) = k (Quotient.mk (gluedRelSetoid d) x))
    (h₂ : ∀ x, Quotient.mk (gluedRelSetoid d') (g₂ x) = k (Quotient.mk (gluedRelSetoid d) x)) :
    g₁ = g₂ := by
  refine hg₁.ext_on hd hg₂ fun x hx ↦
    eq_of_mk_eq_of_notMem_flagPointSet (fun hF ↦ hx ?_) ((h₁ x).trans (h₂ x).symm)
  rw [← preimage_nodeSet] at hF ⊢
  rw [mem_preimage, h₁] at hF
  exact hk _ hF

/-! ### The lift away from the flag points -/

variable [Finite Flag']

private theorem continuousOn_liftAux (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d) :
    ContinuousOn (liftAux h) (flagPointSet d)ᶜ := by
  -- Corestrict to the complement of the flag points, where the quotient map is an embedding.
  let k : ((flagPointSet d)ᶜ : Set (Σ i, X i)) → ((flagPointSet d')ᶜ : Set (Σ i, X' i)) :=
    fun x ↦ ⟨liftAux h x, (mem_flagPointSet_iff_of_mk_eq hN (mk_liftAux h x)).not.mpr x.2⟩
  have hk : Continuous k := by
    rw [(isOpenEmbedding_domRestrict_quotient_mk d').isInducing.continuous_iff]
    have : (flagPointSet d')ᶜ.domRestrict (Quotient.mk (gluedRelSetoid d')) ∘ k =
        fun x : ((flagPointSet d)ᶜ : Set (Σ i, X i)) ↦ h (Quotient.mk (gluedRelSetoid d) x) :=
      funext fun x ↦ mk_liftAux h x
    rw [this]
    exact h.continuous.comp (continuous_quotient_mk'.comp continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hk)

/-- The lift of `h`: the continuous extension of the lift away from the flag points. -/
private def liftMap (h : GluedCurve d ≃ₜ GluedCurve d') : (Σ i, X i) → Σ i, X' i :=
  extendFrom (flagPointSet d)ᶜ (liftAux h)

private theorem liftMap_eq_liftAux (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d) {x : Σ i, X i} (hx : x ∉ flagPointSet d) :
    liftMap h x = liftAux h x :=
  extendFrom_extends (continuousOn_liftAux h hN) x hx

variable [∀ i, T2Space (X i)] [Finite Flag]

/-! ### The branch at a flag point -/

/-- **Choice of branch.**  Near a flag point `p` with connected punctured neighbourhoods, the lift
away from the flag points tends to a single point over the image under `h` of the node of `p`. -/
private theorem exists_tendsto_liftAux (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d)
    (hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}))
    {p : Σ i, X i} (hp : p ∈ flagPointSet d) :
    ∃ q, Quotient.mk (gluedRelSetoid d') q = h (Quotient.mk (gluedRelSetoid d) p) ∧
      Tendsto (liftAux h) (𝓝[(flagPointSet d)ᶜ] p) (𝓝 q) := by
  let S := Quotient.mk (gluedRelSetoid d') ⁻¹' {h (Quotient.mk (gluedRelSetoid d) p)}
  have : (𝓝[(flagPointSet d)ᶜ] p).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp ((dense_compl_flagPointSet hX) p)
  -- The fibre over the node is a finite set of flag points.
  have hS : S.Finite := (flagPointSet_finite d').subset fun y hy ↦
    (mem_flagPointSet_iff_of_mk_eq hN hy).mpr hp
  -- The lift tends to that fibre, because the quotient map is closed.
  have hfS : Tendsto (liftAux h) (𝓝[(flagPointSet d)ᶜ] p) (𝓝ˢ S) := by
    refine (Tendsto.mono_left ?_ nhdsWithin_le_nhds).mono_right
      (Setoid.isClosedMap_quotient_mk (gluedRelSetoid d') (flagPointSet_finite d')
        (mem_flagPointSet_of_gluedRelSetoid_of_ne d')).comap_nhds_le
    rw [tendsto_comap_iff]
    have : Quotient.mk (gluedRelSetoid d') ∘ liftAux h =
        fun x ↦ h (Quotient.mk (gluedRelSetoid d) x) := funext fun x ↦ mk_liftAux h x
    rw [this]
    exact (h.continuous.comp continuous_quotient_mk').tendsto p
  -- Arbitrarily small punctured neighbourhoods of `p` have connected images.
  have hconn : ∀ s ∈ 𝓝[(flagPointSet d)ᶜ] p, ∃ t ∈ 𝓝[(flagPointSet d)ᶜ] p,
      t ⊆ s ∧ IsPreconnected (liftAux h '' t) := by
    intro s hs
    obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs
    obtain ⟨V, hV, hVU, hVF, hVc⟩ :=
      exists_mem_nhds_isConnected_sdiff_singleton_subset_compl_flagPointSet (d := d) (hX p hp) hU
    have hVp : V ∩ (flagPointSet d)ᶜ ⊆ V \ {p} := fun y hy ↦
      ⟨hy.1, fun hyp ↦ hy.2 (by rw [mem_singleton_iff.mp hyp]; exact hp)⟩
    refine ⟨V \ {p}, mem_of_superset (inter_mem_nhdsWithin _ hV) ?_, ?_,
      hVc.isPreconnected.image _ ((continuousOn_liftAux h hN).mono hVF)⟩
    · exact fun y hy ↦ hVp ⟨hy.2, hy.1⟩
    · exact fun y hy ↦ hUs ⟨hVU hy.1, hVF hy⟩
  obtain ⟨q, hq, hfq⟩ := hfS.exists_mem_tendsto_nhds hS hconn
  exact ⟨q, mem_singleton_iff.mp (mem_preimage.mp hq), hfq⟩

/-! ### The lift -/

private theorem tendsto_liftAux_and_mk_liftMap (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d)
    (hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}))
    (x : Σ i, X i) :
    Tendsto (liftAux h) (𝓝[(flagPointSet d)ᶜ] x) (𝓝 (liftMap h x)) ∧
      Quotient.mk (gluedRelSetoid d') (liftMap h x) = h (Quotient.mk (gluedRelSetoid d) x) := by
  by_cases hx : x ∈ flagPointSet d
  · obtain ⟨q, hq, hfq⟩ := exists_tendsto_liftAux h hN hX hx
    have : liftMap h x = q := extendFrom_eq ((dense_compl_flagPointSet hX) x) hfq
    rw [this]
    exact ⟨hfq, hq⟩
  · rw [liftMap_eq_liftAux h hN hx]
    exact ⟨continuousOn_liftAux h hN x hx, mk_liftAux h x⟩

private theorem mk_liftMap (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d)
    (hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}))
    (x : Σ i, X i) :
    Quotient.mk (gluedRelSetoid d') (liftMap h x) = h (Quotient.mk (gluedRelSetoid d) x) :=
  (tendsto_liftAux_and_mk_liftMap h hN hX x).2

private theorem continuous_liftMap (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d)
    (hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})) :
    Continuous (liftMap h) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  -- A neighbourhood of `x` consists of `x` and points which are not flag points.
  have hF : {x} ∪ (flagPointSet d)ᶜ ∈ 𝓝 x := by
    rw [← compl_sdiff]
    exact (flagPointSet_finite d).sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  have hfx : liftMap h =ᶠ[𝓝[(flagPointSet d)ᶜ] x] liftAux h :=
    eventually_nhdsWithin_of_forall fun y hy ↦ liftMap_eq_liftAux h hN hy
  rw [ContinuousAt, ← nhdsWithin_eq_nhds.mpr hF, nhdsWithin_union, nhdsWithin_singleton]
  exact tendsto_sup.mpr ⟨tendsto_pure_nhds _ _,
    (tendsto_liftAux_and_mk_liftMap h hN hX x).1.congr' hfx.symm⟩

/-- **Lifting node-preserving homeomorphisms.**  A homeomorphism `h` of glued curves mapping
nodes exactly to nodes lifts to a homeomorphism of the normalizations, provided the flag points
on both sides have arbitrarily small neighbourhoods with connected punctured versions. The lift
covers `h` (`mk_liftHomeomorph`) and is the unique continuous map doing so
(`eq_liftHomeomorph`). -/
def liftHomeomorph (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d)
    (hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}))
    (hX' : ∀ x ∈ flagPointSet d', ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})) :
    (Σ i, X i) ≃ₜ (Σ i, X' i) :=
  have hN' : ∀ z, h.symm z ∈ nodeSet d ↔ z ∈ nodeSet d' := fun z ↦ by
    rw [← hN, Homeomorph.apply_symm_apply]
  { toFun := liftMap h
    invFun := liftMap h.symm
    left_inv := congrFun (eq_of_mk_eq_mk (k := id) (fun _ ↦ id) (dense_compl_flagPointSet hX)
      ((continuous_liftMap h.symm hN' hX').comp (continuous_liftMap h hN hX)) continuous_id
      (fun x ↦ by simp [mk_liftMap _ hN' hX', mk_liftMap _ hN hX]) fun _ ↦ rfl)
    right_inv := congrFun (eq_of_mk_eq_mk (k := id) (fun _ ↦ id) (dense_compl_flagPointSet hX')
      ((continuous_liftMap h hN hX).comp (continuous_liftMap h.symm hN' hX')) continuous_id
      (fun x ↦ by simp [mk_liftMap _ hN' hX', mk_liftMap _ hN hX]) fun _ ↦ rfl)
    continuous_toFun := continuous_liftMap h hN hX
    continuous_invFun := continuous_liftMap h.symm hN' hX' }

section liftHomeomorph

variable {h : GluedCurve d ≃ₜ GluedCurve d'} {hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d}
  {hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})}
  {hX' : ∀ x ∈ flagPointSet d', ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})}

/-- **The lift covers `h`.** -/
@[simp] theorem mk_liftHomeomorph (x : Σ i, X i) :
    Quotient.mk (gluedRelSetoid d') (liftHomeomorph h hN hX hX' x) =
      h (Quotient.mk (gluedRelSetoid d) x) :=
  mk_liftMap h hN hX x

/-- The inverse of the lift of `h` is the lift of the inverse of `h`. -/
theorem liftHomeomorph_symm :
    (liftHomeomorph h hN hX hX').symm = liftHomeomorph h.symm
      (fun z ↦ by rw [← hN, Homeomorph.apply_symm_apply]) hX' hX :=
  (rfl)

/-- **Uniqueness of the lift.**  A continuous map of the normalizations covering `h` is the
lift of `h`. -/
theorem eq_liftHomeomorph {g : (Σ i, X i) → Σ i, X' i} (hg : Continuous g)
    (hgh : ∀ x, Quotient.mk (gluedRelSetoid d') (g x) = h (Quotient.mk (gluedRelSetoid d) x)) :
    g = liftHomeomorph h hN hX hX' :=
  eq_of_mk_eq_mk (fun z ↦ (hN z).mp) (dense_compl_flagPointSet hX) hg
    (liftHomeomorph h hN hX hX').continuous hgh (mk_liftHomeomorph (hX' := hX'))

-- High priority, so that `simp` removes the lift before `mem_flagPointSet` unfolds the
-- membership into an existential that no longer mentions `flagPointSet`.
/-- The lift maps flag points exactly to flag points. -/
@[simp high] theorem liftHomeomorph_mem_flagPointSet_iff (x : Σ i, X i) :
    liftHomeomorph h hN hX hX' x ∈ flagPointSet d' ↔ x ∈ flagPointSet d :=
  mem_flagPointSet_iff_of_mk_eq hN (mk_liftHomeomorph x)

/-- **The lift respects flag pairs.**  The lift carries the two points of a flag pair exactly to
the two points of a flag pair. -/
@[simp] theorem flagRel_liftHomeomorph_iff (x y : Σ i, X i) :
    flagRel d' (liftHomeomorph h hN hX hX' x) (liftHomeomorph h hN hX hX' y) ↔ flagRel d x y := by
  rw [flagRel_iff_mk_eq_and_ne, flagRel_iff_mk_eq_and_ne, mk_liftHomeomorph, mk_liftHomeomorph,
    h.injective.eq_iff, (liftHomeomorph h hN hX hX').injective.ne_iff]

end liftHomeomorph

/-! ### Lifting isomorphisms of nodal curves -/

namespace Iso

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [∀ i, ChartedSpace H (X i)] [∀ i, ChartedSpace H (X' i)]
  {hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})}
  {hX' : ∀ x ∈ flagPointSet d', ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})}

/-- **Lifting recovers an isomorphism from its descent.**  The lift of the homeomorphism of glued
curves induced by an isomorphism of nodal curves is the isomorphism itself. -/
@[simp] theorem liftHomeomorph_gluedCurveHomeomorph (e : Iso I n d d') :
    ⇑(liftHomeomorph e.gluedCurveHomeomorph e.gluedCurveHomeomorph_mem_nodeSet_iff hX hX') = e :=
  (eq_liftHomeomorph e.continuous fun _ ↦ (gluedCurveHomeomorph_mk e _).symm).symm

variable (I n) in
/-- **Lifting an isomorphism of glued curves.**  A homeomorphism of glued curves mapping nodes
exactly to nodes, whose lift to the normalizations is `C^n` in both directions, is induced by an
isomorphism of nodal curves (`gluedCurveHomeomorph_ofGluedCurveHomeomorph`). -/
def ofGluedCurveHomeomorph (h : GluedCurve d ≃ₜ GluedCurve d')
    (hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d)
    (hX : ∀ x ∈ flagPointSet d, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}))
    (hX' : ∀ x ∈ flagPointSet d', ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}))
    (hφ : ContMDiff I I n (liftHomeomorph h hN hX hX'))
    (hψ : ContMDiff I I n (liftHomeomorph h hN hX hX').symm) : Iso I n d d' where
  toDiffeomorph :=
    { toEquiv := (liftHomeomorph h hN hX hX').toEquiv
      contMDiff_toFun := hφ
      contMDiff_invFun := hψ }
  flagRel_apply_iff' := flagRel_liftHomeomorph_iff (hN := hN) (hX := hX) (hX' := hX')

section ofGluedCurveHomeomorph

variable {h : GluedCurve d ≃ₜ GluedCurve d'} {hN : ∀ z, h z ∈ nodeSet d' ↔ z ∈ nodeSet d}
  {hφ : ContMDiff I I n (liftHomeomorph h hN hX hX')}
  {hψ : ContMDiff I I n (liftHomeomorph h hN hX hX').symm}

/-- The isomorphism lifting `h` acts as the lift of `h`. -/
@[simp] theorem coe_ofGluedCurveHomeomorph :
    ⇑(ofGluedCurveHomeomorph I n h hN hX hX' hφ hψ) = liftHomeomorph h hN hX hX' :=
  coe_mk _ _

/-- **Descent undoes lifting.**  The isomorphism lifting `h` induces `h` on the glued curves. -/
@[simp] theorem gluedCurveHomeomorph_ofGluedCurveHomeomorph :
    (ofGluedCurveHomeomorph I n h hN hX hX' hφ hψ).gluedCurveHomeomorph = h :=
  Homeomorph.ext fun z ↦ Quotient.inductionOn z fun x ↦ by
    rw [gluedCurveHomeomorph_mk, coe_ofGluedCurveHomeomorph, mk_liftHomeomorph]

end ofGluedCurveHomeomorph

/-- **Lifting undoes descent.**  Lifting the homeomorphism of glued curves induced by an
isomorphism of nodal curves recovers the isomorphism. -/
@[simp] theorem ofGluedCurveHomeomorph_gluedCurveHomeomorph (e : Iso I n d d')
    {hφ : ContMDiff I I n
      (liftHomeomorph e.gluedCurveHomeomorph e.gluedCurveHomeomorph_mem_nodeSet_iff hX hX')}
    {hψ : ContMDiff I I n
      (liftHomeomorph e.gluedCurveHomeomorph e.gluedCurveHomeomorph_mem_nodeSet_iff hX hX').symm} :
    ofGluedCurveHomeomorph I n e.gluedCurveHomeomorph e.gluedCurveHomeomorph_mem_nodeSet_iff
      hX hX' hφ hψ = e :=
  Iso.ext fun x ↦ by
    rw [coe_ofGluedCurveHomeomorph, liftHomeomorph_gluedCurveHomeomorph]

end Iso

end NodalGluing

end TauCeti
