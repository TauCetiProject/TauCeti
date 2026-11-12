/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Transporting orientations along fibrewise isomorphisms

Let `E' → B'` and `E → B` be real vector bundles with model fibres `F'` and `F`, let `g : B' → B`
be a continuous map, and let `φ b' : E'_{b'} ≃ E_{g b'}` be a family of continuous linear
equivalences whose total-space map `v ↦ (g (π v), φ (π v) v)` is continuous. An orientation `o` of
`E` then transports to the orientation `φ^* o` of `E'` that orients the fibre over `b'` as the
pull-back of `o (g b')` along `φ b'` (`TauCeti.VectorBundleOrientation.comap`): it is the unique
family of fibre orientations that `φ` carries to `o`
(`TauCeti.VectorBundleOrientation.map_comap_apply`,
`TauCeti.VectorBundleOrientation.eq_comap_iff`).

These fibre orientations vary continuously because, read in linear trivializations of `E'` and
`E`, the fibrewise isomorphism is a continuous family of linear maps `F' → F`
(`TauCeti.continuousOn_fiberwise_inCoordinates`): composed with
the inverse of its value at a base point, it is a continuous family of endomorphisms of `F'` with
determinant `1` at that point, hence of positive determinant nearby, and such endomorphisms fix
orientations.

The pullback of an orientation along a continuous map of bases
(`TauCeti.VectorBundleOrientation.pullback`) is the case where `E'` is the pullback bundle and
every `φ b'` is the identity. The Thom and Euler classes of transported orientations are computed
in `TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv`.

## Main definitions

* `TauCeti.VectorBundleOrientation.comap`: the transport of an orientation along a fibrewise
  isomorphism of vector bundles.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (oriented vector bundles and orientation-preserving bundle maps).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Topology

namespace TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {B' : Type*} [TopologicalSpace B']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {E' : B' → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  {ι : Type*} [Fintype ι] {g : C(B', B)} {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}

namespace VectorBundleOrientation

/-- Near `x₀`, a linear equivalence `f : F' ≃ F` transports an orientation `c` of `F'` as `f₀` does
whenever `f₀⁻¹ ∘ f` is the value at `x` of a family `L` of endomorphisms of `F'` that is continuous
at `x₀` with value the identity there: the determinant of `L x` stays positive near `x₀`. -/
private theorem eventually_map_eq_map_of_continuousAt {X : Type*} [TopologicalSpace X] {x₀ : X}
    (hι : Fintype.card ι = finrank ℝ F') (c : Orientation ℝ F' ι) (f₀ : F' ≃L[ℝ] F)
    {L : X → F' →L[ℝ] F'} (hL : FiniteDimensional ℝ F' → ContinuousAt L x₀)
    (hL₀ : L x₀ = ContinuousLinearMap.id ℝ F') :
    ∀ᶠ x in 𝓝 x₀, ∀ f : F' ≃L[ℝ] F, (f.trans f₀.symm : F' →L[ℝ] F') = L x →
      Orientation.map ι f.toLinearEquiv c = Orientation.map ι f₀.toLinearEquiv c := by
  rcases isEmpty_or_nonempty ι with hι₀ | hι₀
  · -- With `ι` empty, transport along any self-equivalence of `F'` fixes every orientation.
    refine Eventually.of_forall fun x f _ ↦ ?_
    have h := Orientation.map_of_isEmpty (x := c)
      (f := f.toLinearEquiv.trans f₀.toLinearEquiv.symm)
    rw [Orientation.map_trans, ← Orientation.map_symm, Equiv.symm_apply_eq] at h
    exact h
  -- Otherwise `F'` is finite-dimensional, and the determinant of `L x` is positive near `x₀`.
  have : FiniteDimensional ℝ F' := Module.finite_of_finrank_pos (hι ▸ Fintype.card_pos)
  have hLb : (L x₀).det = 1 := by
    rw [hL₀]
    exact LinearMap.det_id
  filter_upwards [(ContinuousLinearMap.continuous_det.continuousAt.comp (hL this)).eventually
    (lt_mem_nhds (hLb ▸ one_pos))] with x hx f hf
  refine Orientation.map_eq_map_of_det_pos c _ _ hι ?_
  rw [Function.comp_apply, ← hf] at hx
  exact hx

/-- Near a point `b'`, the fibre orientations obtained by pulling back `o` along `φ` are locally
constant when read in the preferred trivialization of `E'` at `b'`. -/
private theorem eventually_mapOrientation_comap (hι : Fintype.card ι = finrank ℝ F')
    (o : VectorBundleOrientation F E ι)
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2))
    (b' : B') :
    ∀ᶠ x in 𝓝 b', ∀ hx : x ∈ (trivializationAt F' E' b').baseSet,
      (trivializationAt F' E' b').mapOrientation ι hx
          (Orientation.map ι (φ x).symm.toLinearEquiv (o (g x))) =
        (trivializationAt F' E' b').mapOrientation ι
          (FiberBundle.mem_baseSet_trivializationAt' b')
          (Orientation.map ι (φ b').symm.toLinearEquiv (o (g b'))) := by
  set e' := trivializationAt F' E' b'
  set e := trivializationAt F E (g b')
  have hb' : b' ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' b'
  have hb : g b' ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (g b')
  -- The fibrewise isomorphism over `x`, read in `e'` and `e`.
  let T (x : B') (hx' : x ∈ e'.baseSet) (hx : g x ∈ e.baseSet) : F' ≃L[ℝ] F :=
    (e'.continuousLinearEquivAt ℝ x hx').symm.trans
      ((φ x).trans (e.continuousLinearEquivAt ℝ (g x) hx))
  -- It carries the reading in `e'` of the pulled-back orientation to the reading of `o` in `e`.
  have hT (x : B') (hx' : x ∈ e'.baseSet) (hx : g x ∈ e.baseSet) :
      Orientation.map ι (T x hx' hx).toLinearEquiv
          (e'.mapOrientation ι hx' (Orientation.map ι (φ x).symm.toLinearEquiv (o (g x)))) =
        e.mapOrientation ι hx (o (g x)) := by
    have hTl : (T x hx' hx).toLinearEquiv = (e'.linearEquivAt ℝ x hx').symm.trans
        ((φ x).toLinearEquiv.trans (e.linearEquivAt ℝ (g x) hx)) :=
      LinearEquiv.ext fun v ↦ by
        simp [T, e.coe_continuousLinearEquivAt_eq hx, e'.symm_continuousLinearEquivAt_eq hx',
          e.coe_linearMapAt_of_mem hx, e'.symmL_apply hx']
    rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply,
      hTl]
    simp only [Orientation.map_trans, ContinuousLinearEquiv.toLinearEquiv_symm,
      ← Orientation.map_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  set c := e'.mapOrientation ι hb' (Orientation.map ι (φ b').symm.toLinearEquiv (o (g b')))
  -- It remains to see that near `b'` the readings `T x` transport `c` as `T b'` does.
  have hU : e'.baseSet ∩ g ⁻¹' e.baseSet ∈ 𝓝 b' :=
    (e'.open_baseSet.inter (e.open_baseSet.preimage g.continuous)).mem_nhds ⟨hb', hb⟩
  -- Read without membership hypotheses, `(T b')⁻¹ ∘ T x` is continuous at `b'`.
  let L (x : B') : F' →L[ℝ] F' := ((T b' hb' hb).symm : F →L[ℝ] F').comp
    ((e.continuousLinearMapAt ℝ (g x)).comp ((φ x : E' x →L[ℝ] E (g x)).comp (e'.symmL ℝ x)))
  have hL (x : B') (hx' : x ∈ e'.baseSet) (hx : g x ∈ e.baseSet) :
      ((T x hx' hx).trans (T b' hb' hb).symm : F' →L[ℝ] F') = L x := by
    ext v
    simp [L, T, e.coe_continuousLinearEquivAt_eq hx, e'.symm_continuousLinearEquivAt_eq hx']
  have hS := eventually_map_eq_map_of_continuousAt hι c (T b' hb' hb) (L := L)
    (fun _ ↦ (continuousOn_const.clm_comp (continuousOn_fiberwise_inCoordinates
      (φ := fun b' ↦ (φ b' : E' b' →L[ℝ] E (g b'))) hφ e e')).continuousAt hU)
    (by rw [← hL b' hb' hb, ContinuousLinearEquiv.self_trans_symm]; rfl)
  filter_upwards [hU, g.continuous.continuousAt.eventually (o.eventually_mapOrientation_eq' (g b')),
    hS] with x hxU hxo hxS hx'
  refine (Orientation.map ι (T x hx' hxU.2).toLinearEquiv).injective ?_
  calc
    _ = e.mapOrientation ι hxU.2 (o (g x)) := hT x hx' hxU.2
    _ = e.mapOrientation ι hb (o (g b')) := hxo hxU.2
    _ = Orientation.map ι (T b' hb' hb).toLinearEquiv c := (hT b' hb' hb).symm
    _ = _ := (hxS _ (hL x hx' hxU.2)).symm

/-- **The transport of an orientation along a fibrewise isomorphism.** For a fibrewise isomorphism
`φ b' : E'_{b'} ≃ E_{g b'}` over a continuous map `g : B' → B`, with continuous total-space map,
the orientation of `E'` orienting the fibre over `b'` as the pull-back of `o (g b')` along `φ b'`.
This needs `ι` to have cardinality the rank of `E'`. -/
def comap (hι : Fintype.card ι = finrank ℝ F') (o : VectorBundleOrientation F E ι)
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    VectorBundleOrientation F' E' ι where
  toFun b' := Orientation.map ι (φ b').symm.toLinearEquiv (o (g b'))
  eventually_mapOrientation_eq' := eventually_mapOrientation_comap hι o hφ

variable (hι : Fintype.card ι = finrank ℝ F') (o : VectorBundleOrientation F E ι)
  (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2))

theorem comap_apply (b' : B') :
    o.comap hι hφ b' = Orientation.map ι (φ b').symm.toLinearEquiv (o (g b')) :=
  (rfl)

/-- The fibrewise isomorphism `φ` carries the transported orientation to the original one. -/
@[simp]
theorem map_comap_apply (b' : B') :
    Orientation.map ι (φ b').toLinearEquiv (o.comap hι hφ b') = o (g b') := by
  rw [comap_apply, ContinuousLinearEquiv.toLinearEquiv_symm, ← Orientation.map_symm,
    Equiv.apply_symm_apply]

/-- The transported orientation is the only orientation that the fibrewise isomorphism `φ` carries
to `o`. -/
theorem eq_comap_iff (o' : VectorBundleOrientation F' E' ι) :
    o' = o.comap hι hφ ↔ ∀ b', Orientation.map ι (φ b').toLinearEquiv (o' b') = o (g b') := by
  refine ⟨fun h b' ↦ h ▸ map_comap_apply hι o hφ b', fun h ↦ ext fun b' ↦ ?_⟩
  rw [comap_apply, ← h b', ContinuousLinearEquiv.toLinearEquiv_symm, ← Orientation.map_symm,
    Equiv.symm_apply_apply]

@[simp]
theorem comap_neg : (-o).comap hι hφ = -o.comap hι hφ :=
  ext fun b' ↦ Module.Ray.map_neg _ (o (g b'))

end VectorBundleOrientation

end TauCeti
