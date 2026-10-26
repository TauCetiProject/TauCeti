/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.Quotient.Descent
public import TauCeti.Topology.MappingTorus.Basic

/-!
# The smooth mapping torus of a diffeomorphism

For a `C^n` diffeomorphism `φ : M ≃ₘ^n⟮I, I⟯ M` of a manifold, the mapping torus
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` is the orbit space of the action of
`Multiplicative ℤ` on `ℝ × M` by `k • (t, x) = (t + k, φ ^ (-k) x)`. This action is free and
properly discontinuous, because it translates the real coordinate, and it acts by the `C^n` maps
built from the iterates of `φ`. So when `M` is a locally compact Hausdorff `C^n` manifold,
`TauCeti.instIsManifoldQuotient` makes `Y_φ` a Hausdorff `C^n` manifold modelled on
`𝓘(ℝ).prod I` and the orbit projection is a `C^n` local diffeomorphism; `Y_φ` is second countable
when `M` is. No compactness of `M` is needed.

So that `ℝ × M` does not acquire a `φ`-dependent action of `Multiplicative ℤ`, the action lives on
the type synonym `TauCeti.SmoothMappingTorus.Cover φ` of `ℝ × M`, which carries the topology and
the manifold structure of `ℝ × M`; `TauCeti.SmoothMappingTorus.Cover.ofProd φ` identifies the two.

The class `TauCeti.SmoothMappingTorus.mk φ t x` of `(t, x)` satisfies `[t + 1, x] = [t, φ x]`, so
flowing the real coordinate for time one from the fibre at height `t` returns to that fibre by `φ`.
The projection `TauCeti.SmoothMappingTorus.proj φ : Y_φ → UnitAddCircle` sends `[t, x]` to the class
of `t`. It is `C^n`, and for each real `t` the map `x ↦ [t, x]` is an injective `C^n` map of `M`
onto the fibre over the class of `t`. Two choices of the lift `t` differ by an integer `k`, and the
corresponding inclusions differ by `φ ^ k`.

Translating the real coordinate, `[t, x] ↦ [t + s, x]`, is the suspension flow
`TauCeti.SmoothMappingTorus.flow φ`, a complete flow on `Y_φ` that is jointly `C^n` in time and
space when `M` is a locally compact Hausdorff `C^n` manifold. It covers the rotation of the
circle, and its time-one map returns the fibre at height `t` to itself by `φ`. So its closed orbits
are those through the periodic points of `φ`, and the orbit through a point of least period `d`
has least period `d`.

Tau Ceti's topological mapping torus `TauCeti.MappingTorus` of a homeomorphism `ψ` identifies
`(ψ x, t + 1)` with `(x, t)`. The smooth mapping torus of `φ` is homeomorphic to the topological
mapping torus of `φ⁻¹` (`TauCeti.SmoothMappingTorus.homeomorphMappingTorus`), compatibly with the
projections to the circle, so the topological results for `TauCeti.MappingTorus` apply to `Y_φ`.

## Main definitions

* `TauCeti.SmoothMappingTorus.Cover φ`: the product `ℝ × M`, with the action of
  `Multiplicative ℤ` by `k • (t, x) = (t + k, φ ^ (-k) x)`.
* `TauCeti.SmoothMappingTorus φ`: the orbit space of this action, the smooth mapping torus.
* `TauCeti.SmoothMappingTorus.mk φ t x`: the class of `(t, x)`.
* `TauCeti.SmoothMappingTorus.proj φ`: the projection to the circle `UnitAddCircle`.
* `TauCeti.SmoothMappingTorus.flow φ`: the suspension flow `[t, x] ↦ [t + s, x]`.
* `TauCeti.SmoothMappingTorus.flowDiffeomorph φ s`: its time-`s` map, as a diffeomorphism.
* `TauCeti.SmoothMappingTorus.homeomorphMappingTorus φ`: the homeomorphism with the topological
  mapping torus of `φ⁻¹`.

## Main results

* `TauCeti.SmoothMappingTorus.Cover.instProperlyDiscontinuousSMul`,
  `TauCeti.SmoothMappingTorus.Cover.instIsCancelSMul`,
  `TauCeti.SmoothMappingTorus.Cover.instContMDiffConstSMul`: the action is properly
  discontinuous, free and by `C^n` maps, so `SmoothMappingTorus φ` is a `C^n` manifold.
* `TauCeti.SmoothMappingTorus.isLocalDiffeomorph_uncurry_mk`: the quotient map `ℝ × M → Y_φ` is a
  `C^n` local diffeomorphism.
* `TauCeti.SmoothMappingTorus.mk_eq_mk_iff`, `TauCeti.SmoothMappingTorus.mk_add_intCast`: when two
  points of `ℝ × M` have the same class.
* `TauCeti.SmoothMappingTorus.contMDiff_proj`, `TauCeti.SmoothMappingTorus.range_mk`: the
  projection is `C^n`, and its fibres are the images of the fibre inclusions.
* `TauCeti.SmoothMappingTorus.flow_one_mk`: the time-one map of the suspension flow is `φ` on
  each fibre.
* `TauCeti.SmoothMappingTorus.isFixedPt_flow_mk_iff`: `[t, x]` is fixed by the time-`s` map
  exactly when `s` is an integer `k` and `x` is a fixed point of `φ ^ k`.
* `TauCeti.SmoothMappingTorus.isFixedPt_flow_mk_iff_mem_zmultiples`: the periods of the orbit
  through `[t, x]` are the integer multiples of the minimal period of `x` under `φ`.
* `TauCeti.SmoothMappingTorus.contMDiff_uncurry_flow`: the suspension flow is jointly `C^n`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2 (mapping
  tori).
-/

public noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace SmoothMappingTorus

/-- The infinite cyclic cover `ℝ × M` of the mapping torus of `φ`: a type synonym of `ℝ × M`
carrying the action of `Multiplicative ℤ` by `k • (t, x) = (t + k, φ ^ (-k) x)`. -/
@[expose] def Cover (_φ : M ≃ₘ^n⟮I, I⟯ M) : Type _ := ℝ × M

namespace Cover

variable (φ : M ≃ₘ^n⟮I, I⟯ M)

instance : TopologicalSpace (Cover φ) := inferInstanceAs (TopologicalSpace (ℝ × M))

instance [T2Space M] : T2Space (Cover φ) := inferInstanceAs (T2Space (ℝ × M))

instance [LocallyCompactSpace M] : LocallyCompactSpace (Cover φ) :=
  inferInstanceAs (LocallyCompactSpace (ℝ × M))

instance [SecondCountableTopology M] : SecondCountableTopology (Cover φ) :=
  inferInstanceAs (SecondCountableTopology (ℝ × M))

instance : ChartedSpace (ModelProd ℝ H) (Cover φ) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ H) (ℝ × M))

instance {m : ℕ∞ω} [IsManifold I m M] : IsManifold (𝓘(ℝ).prod I) m (Cover φ) :=
  inferInstanceAs (IsManifold (𝓘(ℝ).prod I) m (ℝ × M))

/-- The identification of `ℝ × M` with the cover of the mapping torus of `φ`. -/
def ofProd : ℝ × M ≃ Cover φ := Equiv.refl _

/- `Cover φ` carries the topology and the manifold structure of `ℝ × M`, and `ofProd φ` is the
identity of `ℝ × M`, so its regularity is that of the identity map. -/

/-- The identification of `ℝ × M` with the cover is continuous. -/
theorem continuous_ofProd : Continuous (ofProd φ) := continuous_id

/-- The identification of the cover with `ℝ × M` is continuous. -/
theorem continuous_ofProd_symm : Continuous (ofProd φ).symm := continuous_id

/-- The identification of `ℝ × M` with the cover is `C^m` for every `m`. -/
theorem contMDiff_ofProd (m : ℕ∞ω) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) m (ofProd φ) :=
  contMDiff_id

/-- The identification of the cover with `ℝ × M` is `C^m` for every `m`. -/
theorem contMDiff_ofProd_symm (m : ℕ∞ω) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) m (ofProd φ).symm :=
  contMDiff_id

/-- The identification of `ℝ × M` with the cover is a local diffeomorphism. -/
theorem isLocalDiffeomorph_ofProd (m : ℕ∞ω) :
    IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) m (ofProd φ) :=
  Diffeomorph.isLocalDiffeomorph
    { toEquiv := ofProd φ
      contMDiff_toFun := contMDiff_ofProd φ m
      contMDiff_invFun := contMDiff_ofProd_symm φ m }

/-! ### The action of `Multiplicative ℤ` -/

instance : SMul (Multiplicative ℤ) (Cover φ) where
  smul k z := ofProd φ (((ofProd φ).symm z).1 + k.toAdd, (φ ^ (-k.toAdd)) ((ofProd φ).symm z).2)

/-- The integer `k` acts on the cover by `(t, x) ↦ (t + k, φ ^ (-k) x)`. -/
theorem smul_def (k : Multiplicative ℤ) (z : Cover φ) :
    k • z = ofProd φ (((ofProd φ).symm z).1 + k.toAdd,
      (φ ^ (-k.toAdd)) ((ofProd φ).symm z).2) := (rfl)

/-- The integer `k` acts on the cover by `(t, x) ↦ (t + k, φ ^ (-k) x)`, read in `ℝ × M`. -/
@[simp]
theorem ofProd_symm_smul (k : Multiplicative ℤ) (z : Cover φ) :
    (ofProd φ).symm (k • z) = (((ofProd φ).symm z).1 + k.toAdd,
      (φ ^ (-k.toAdd)) ((ofProd φ).symm z).2) := (rfl)

/-- The integer `k` acts on the cover by `(t, x) ↦ (t + k, φ ^ (-k) x)`, read in `ℝ × M`. -/
@[simp]
theorem smul_ofProd (k : Multiplicative ℤ) (t : ℝ) (x : M) :
    k • ofProd φ (t, x) = ofProd φ (t + k.toAdd, (φ ^ (-k.toAdd)) x) := (rfl)

/-- `Multiplicative ℤ` acts on the cover by `k • (t, x) = (t + k, φ ^ (-k) x)`. -/
instance : MulAction (Multiplicative ℤ) (Cover φ) where
  one_smul z := by simp [smul_def]
  mul_smul j k z := by
    simp only [smul_def, toAdd_mul, Int.cast_add, neg_add, zpow_add, Diffeomorph.mul_apply,
      Equiv.symm_apply_apply]
    congr 2
    ring

/-- The action is by homeomorphisms. -/
instance : ContinuousConstSMul (Multiplicative ℤ) (Cover φ) where
  continuous_const_smul k := by
    simp_rw [smul_def]
    exact (continuous_ofProd φ).comp
      ((((continuous_ofProd_symm φ).fst).add continuous_const).prodMk
        ((φ ^ (-k.toAdd)).continuous.comp (continuous_ofProd_symm φ).snd))

/-- The action is by `C^n` maps. -/
instance instContMDiffConstSMul :
    ContMDiffConstSMul (𝓘(ℝ).prod I) n (Multiplicative ℤ) (Cover φ) where
  contMDiff_const_smul k := by
    simp_rw [smul_def]
    exact (contMDiff_ofProd φ n).comp
      (((contMDiff_fst.add contMDiff_const).prodMk
        ((φ ^ (-k.toAdd)).contMDiff.comp contMDiff_snd)).comp (contMDiff_ofProd_symm φ n))

/-- The action is free: a nontrivial element translates the real coordinate by a nonzero
integer. -/
instance instIsCancelSMul : IsCancelSMul (Multiplicative ℤ) (Cover φ) where
  left_cancel' k _ _ h := smul_left_cancel k h
  right_cancel' j k z h := by
    have h' : (j.toAdd : ℝ) = k.toAdd := by
      simpa using congrArg (fun w ↦ ((ofProd φ).symm w).1) h
    exact Multiplicative.toAdd.injective (by exact_mod_cast h')

/-- The action is properly discontinuous: only finitely many integers translate a compact set to
meet another compact set. -/
instance instProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul (Multiplicative ℤ) (Cover φ) where
  finite_disjoint_inter_image {K L} hK hL := by
    -- If `k • z ∈ L` for some `z ∈ K`, then `k` is the difference of the real coordinates of a
    -- point of `L` and a point of `K`, which lies in a compact set.
    have hC : IsCompact
        ((fun w : Cover φ × Cover φ ↦ ((ofProd φ).symm w.1).1 - ((ofProd φ).symm w.2).1) ''
          L ×ˢ K) :=
      (hL.prod hK).image
        (((continuous_ofProd_symm φ).fst.comp continuous_fst).sub
          ((continuous_ofProd_symm φ).fst.comp continuous_snd))
    have hfin := tendsto_cofinite_cocompact_iff.mp Int.tendsto_coe_cofinite _ hC
    refine (hfin.preimage Multiplicative.toAdd.injective.injOn).subset fun k hk ↦ ?_
    obtain ⟨_, ⟨z, hz, rfl⟩, hkz⟩ := hk
    exact ⟨(k • z, z), ⟨hkz, hz⟩, by simp⟩

end Cover

end SmoothMappingTorus

/-- The smooth mapping torus `(ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` of a `C^n` diffeomorphism `φ`:
the orbit space of the action of `Multiplicative ℤ` on `ℝ × M` by
`k • (t, x) = (t + k, φ ^ (-k) x)`. It is a `C^n` manifold modelled on `𝓘(ℝ).prod I` when `M` is
a locally compact Hausdorff `C^n` manifold. -/
abbrev SmoothMappingTorus (φ : M ≃ₘ^n⟮I, I⟯ M) : Type _ :=
  MulAction.orbitRel.Quotient (Multiplicative ℤ) (SmoothMappingTorus.Cover φ)

namespace SmoothMappingTorus

open Cover

variable (φ : M ≃ₘ^n⟮I, I⟯ M)

/-- The mapping torus of a diffeomorphism of a second countable manifold is second countable. -/
instance [SecondCountableTopology M] : SecondCountableTopology (SmoothMappingTorus φ) :=
  ContinuousConstSMul.secondCountableTopology

/-- The class `[t, x]` of `(t, x) ∈ ℝ × M` in the mapping torus. For fixed `t`, `mk φ t` is the
inclusion of `M` as the fibre over the class of `t` in the circle. -/
def mk (t : ℝ) (x : M) : SmoothMappingTorus φ :=
  Quotient.mk _ (ofProd φ (t, x))

/-- Every point of the mapping torus is the class of a point of `ℝ × M`. -/
theorem uncurry_mk_surjective : Function.Surjective (Function.uncurry (mk φ)) := fun z ↦ by
  obtain ⟨w, rfl⟩ := Quotient.mk_surjective z
  obtain ⟨⟨t, x⟩, rfl⟩ := (ofProd φ).surjective w
  exact ⟨(t, x), rfl⟩

/-- The quotient map `ℝ × M → SmoothMappingTorus φ` is continuous. -/
theorem continuous_uncurry_mk : Continuous (Function.uncurry (mk φ)) :=
  continuous_quot_mk.comp (continuous_ofProd φ)

/-- Two points of `ℝ × M` have the same class in the mapping torus exactly when they differ by
the action of an integer. -/
theorem mk_eq_mk_iff {t s : ℝ} {x y : M} :
    mk φ t x = mk φ s y ↔ ∃ k : ℤ, t = s + k ∧ x = (φ ^ (-k)) y := by
  rw [mk, mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, hk⟩
    have h := congrArg (ofProd φ).symm hk
    simp only [smul_ofProd, Equiv.symm_apply_apply, Prod.mk.injEq] at h
    exact ⟨k.toAdd, h.1.symm, h.2.symm⟩
  · rintro ⟨k, rfl, rfl⟩
    exact ⟨Multiplicative.ofAdd k, by simp⟩

/-- Moving the real coordinate by an integer `k` changes the fibre coordinate by `φ ^ k`. -/
@[simp]
theorem mk_add_intCast (t : ℝ) (k : ℤ) (x : M) : mk φ (t + k) x = mk φ t ((φ ^ k) x) :=
  (mk_eq_mk_iff φ).2 ⟨k, rfl, by simp⟩

/-- Moving the real coordinate once around the circle changes the fibre coordinate by `φ`. -/
@[simp]
theorem mk_add_one (t : ℝ) (x : M) : mk φ (t + 1) x = mk φ t (φ x) := by
  simpa using mk_add_intCast φ t 1 x

/-- The inclusion `x ↦ [t, x]` of the fibre at height `t` is injective. -/
theorem mk_injective (t : ℝ) : Function.Injective (mk φ t) := fun x y h ↦ by
  obtain ⟨k, hk, rfl⟩ := (mk_eq_mk_iff φ).1 h
  obtain rfl : k = 0 := by exact_mod_cast (add_eq_left.mp hk.symm)
  simp

section Manifold

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- The quotient map `ℝ × M → SmoothMappingTorus φ` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_uncurry_mk :
    IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) n (Function.uncurry (mk φ)) := by
  -- By definition, `mk φ` is the orbit projection after the identification `ofProd φ`.
  have h : Function.uncurry (mk φ) =
      Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (Cover φ)) ∘ ofProd φ := (rfl)
  rw [h]
  intro p
  have hq : IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) n
      (Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (Cover φ))) :=
    isLocalDiffeomorph_quotientMk
  exact (isLocalDiffeomorph_ofProd φ n p).comp _ _ (hq _)

/-- The quotient map `ℝ × M → SmoothMappingTorus φ` is `C^n`. -/
theorem contMDiff_uncurry_mk :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) n (Function.uncurry (mk φ)) :=
  (isLocalDiffeomorph_uncurry_mk φ).contMDiff

/-- The inclusion `x ↦ [t, x]` of the fibre at height `t` is `C^n`. -/
theorem contMDiff_mk (t : ℝ) : ContMDiff I (𝓘(ℝ).prod I) n (mk φ t) :=
  (contMDiff_uncurry_mk φ).comp (contMDiff_const.prodMk contMDiff_id)

end Manifold

/-! ### The projection to the circle -/

/-- The projection `[t, x] ↦ [t]` of the mapping torus to the circle `UnitAddCircle`. -/
def proj : SmoothMappingTorus φ → UnitAddCircle :=
  MulAction.orbitRelQuotientLift (fun z ↦ (((ofProd φ).symm z).1 : UnitAddCircle))
    fun k z ↦ by simp

/-- The projection sends `[t, x]` to the class of `t`. -/
@[simp]
theorem proj_mk (t : ℝ) (x : M) : proj φ (mk φ t x) = t :=
  MulAction.orbitRelQuotientLift_mk _

/-- The projection of the mapping torus of a diffeomorphism of a nonempty manifold to the circle
is surjective. -/
theorem proj_surjective [Nonempty M] : Function.Surjective (proj φ) := by
  intro θ
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact ⟨mk φ t (Classical.arbitrary M), proj_mk φ _ _⟩

/-- The fibre of the projection over the class of `t` is the image of the inclusion
`x ↦ [t, x]`. -/
theorem range_mk (t : ℝ) : range (mk φ t) = proj φ ⁻¹' {(t : UnitAddCircle)} := by
  refine Subset.antisymm (range_subset_iff.2 fun x ↦ proj_mk φ t x) fun z hz ↦ ?_
  obtain ⟨⟨s, y⟩, rfl⟩ := uncurry_mk_surjective φ z
  have hs : ((s : ℝ) : UnitAddCircle) = t := by simpa using hz
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hs)
  have ht : t = s + k := by rw [zsmul_one] at hk; linarith
  refine ⟨(φ ^ (-k)) y, ?_⟩
  rw [Function.uncurry_apply_pair, ht, mk_add_intCast]
  simp

/-- The projection of the mapping torus to the circle is `C^n`. -/
theorem contMDiff_proj [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (proj φ) :=
  (contMDiff_orbitRelQuotientLift_iff le_rfl).2
    ((AddCircle.contMDiff_coe 1 n).comp (contMDiff_fst.comp (contMDiff_ofProd_symm φ n)))

/-! ### The suspension flow -/

/-- The time-`s` map `[t, x] ↦ [t + s, x]` of the suspension flow, before it is bundled as a
flow. -/
private def translate (s : ℝ) : SmoothMappingTorus φ → SmoothMappingTorus φ :=
  MulAction.orbitRelQuotientLift
    (fun z ↦ mk φ (((ofProd φ).symm z).1 + s) ((ofProd φ).symm z).2) fun k z ↦ by
      rw [ofProd_symm_smul, add_right_comm, mk_add_intCast]
      simp

/-- The time-`s` map sends `[t, x]` to `[t + s, x]`. -/
private theorem translate_mk (s t : ℝ) (x : M) : translate φ s (mk φ t x) = mk φ (t + s) x := by
  rw [translate, mk, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- The suspension flow of `φ` on its mapping torus: the time-`s` map translates the real
coordinate, `[t, x] ↦ [t + s, x]` (`TauCeti.SmoothMappingTorus.flow_mk`). It covers the rotation
of the circle by `s` (`TauCeti.SmoothMappingTorus.proj_flow`), and its time-one map returns each
fibre to itself by `φ` (`TauCeti.SmoothMappingTorus.flow_one_mk`). -/
def flow : Flow ℝ (SmoothMappingTorus φ) where
  toFun := translate φ
  cont' := by
    -- `ℝ × Y_φ` is the open quotient of `ℝ × Cover φ`, where the flow is a translation.
    refine (IsOpenQuotientMap.id.prodMap (MulAction.isOpenQuotientMap_quotientMk
      (Γ := Multiplicative ℤ) (T := Cover φ))).continuous_comp_iff.1 ?_
    refine ((continuous_uncurry_mk φ).comp
      ((((continuous_ofProd_symm φ).fst.comp continuous_snd).add continuous_fst).prodMk
        ((continuous_ofProd_symm φ).snd.comp continuous_snd))).congr fun ⟨s, w⟩ ↦ ?_
    obtain ⟨⟨t, x⟩, rfl⟩ := (ofProd φ).surjective w
    exact (translate_mk φ s t x).symm
  map_add' s₁ s₂ z := by
    obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    simp only [Function.uncurry_apply_pair, translate_mk, add_assoc, add_comm s₂]
  map_zero' z := by
    obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    simp only [Function.uncurry_apply_pair, translate_mk, add_zero]

/-- The suspension flow translates the real coordinate: `[t, x] ↦ [t + s, x]`. -/
@[simp]
theorem flow_mk (s t : ℝ) (x : M) : flow φ s (mk φ t x) = mk φ (t + s) x :=
  translate_mk φ s t x

/-- The suspension flow covers the rotation of the circle: it moves the projection by `s`. -/
@[simp]
theorem proj_flow (s : ℝ) (z : SmoothMappingTorus φ) : proj φ (flow φ s z) = proj φ z + s := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The time-`k` map of the suspension flow, for an integer `k`, returns each fibre to itself
by `φ ^ k`. -/
theorem flow_intCast_mk (k : ℤ) (t : ℝ) (x : M) : flow φ k (mk φ t x) = mk φ t ((φ ^ k) x) := by
  simp

/-- The time-one map of the suspension flow returns each fibre to itself by `φ`: it is the first
return map of the flow to the fibre at height `t`. -/
theorem flow_one_mk (t : ℝ) (x : M) : flow φ 1 (mk φ t x) = mk φ t (φ x) := by
  simp

/-- A point `[t, x]` is fixed by the time-`s` map of the suspension flow exactly when `s` is an
integer `k` and `x` is a fixed point of `φ ^ k`. So the closed orbits of the flow are those
through the periodic points of `φ`, with integer periods. -/
theorem isFixedPt_flow_mk_iff {s t : ℝ} {x : M} :
    Function.IsFixedPt (flow φ s) (mk φ t x) ↔
      ∃ k : ℤ, s = k ∧ Function.IsFixedPt (φ ^ k) x := by
  rw [Function.IsFixedPt, flow_mk, mk_eq_mk_iff]
  refine exists_congr fun k ↦ and_congr (add_right_inj t) ?_
  rw [Function.IsFixedPt, zpow_neg, eq_comm, Diffeomorph.inv_apply]
  exact ⟨fun h ↦ by rw [← h, Diffeomorph.apply_symm_apply, h],
    fun h ↦ by rw [← h, Diffeomorph.symm_apply_apply, h]⟩

/-- The periods of the orbit of the suspension flow through `[t, x]` are the integer multiples of
the minimal period of `x` under `φ`. So the orbit through a periodic point of least period `d` is
closed with least period `d`, and the orbit through a point that is not periodic is not closed. -/
theorem isFixedPt_flow_mk_iff_mem_zmultiples {s t : ℝ} {x : M} :
    Function.IsFixedPt (flow φ s) (mk φ t x) ↔
      s ∈ AddSubgroup.zmultiples (Function.minimalPeriod φ x : ℝ) := by
  have h := φ.isFixedPt_zpow_iff_minimalPeriod_dvd x
  rw [isFixedPt_flow_mk_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl, hk⟩
    obtain ⟨m, rfl⟩ := (h k).1 hk
    exact ⟨m, by push_cast; ring⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m * Function.minimalPeriod φ x, by push_cast; ring, (h _).2 (dvd_mul_left _ _)⟩

section Manifold

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- The suspension flow is jointly `C^n` in time and space. -/
theorem contMDiff_uncurry_flow :
    ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod I) n (Function.uncurry (flow φ)) := by
  -- Precomposed with the quotient map `ℝ × M → Y_φ` in the second factor, the flow is
  -- `(s, t, x) ↦ [t + s, x]`.
  rw [← (isLocalDiffeomorph_uncurry_mk φ).contMDiff_comp_prodMap_iff (uncurry_mk_surjective φ)
    le_rfl]
  have h : Function.uncurry (flow φ) ∘ Prod.map id (Function.uncurry (mk φ)) =
      Function.uncurry (mk φ) ∘ fun p : ℝ × ℝ × M ↦ (p.2.1 + p.1, p.2.2) := by
    funext ⟨s, t, x⟩
    simp
  rw [h]
  exact (contMDiff_uncurry_mk φ).comp
    (((contMDiff_fst.comp contMDiff_snd).add contMDiff_fst).prodMk
      (contMDiff_snd.comp contMDiff_snd))

/-- Each time-`s` map of the suspension flow is `C^n`. -/
theorem contMDiff_flow (s : ℝ) : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) n (flow φ s) :=
  (contMDiff_uncurry_flow φ).comp (contMDiff_const.prodMk contMDiff_id)

/-- The time-`s` map of the suspension flow, as a `C^n` diffeomorphism of the mapping torus with
inverse the time-`(-s)` map. -/
def flowDiffeomorph (s : ℝ) :
    SmoothMappingTorus φ ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod I⟯ SmoothMappingTorus φ where
  toEquiv := ((flow φ).toHomeomorph s).toEquiv
  contMDiff_toFun := contMDiff_flow φ s
  contMDiff_invFun := contMDiff_flow φ (-s)

/-- The diffeomorphism `flowDiffeomorph φ s` is the time-`s` map of the suspension flow. -/
@[simp]
theorem coe_flowDiffeomorph (s : ℝ) : ⇑(flowDiffeomorph φ s) = flow φ s := (rfl)

/-- The inverse of the time-`s` map of the suspension flow is its time-`(-s)` map. -/
@[simp]
theorem flowDiffeomorph_symm (s : ℝ) : (flowDiffeomorph φ s).symm = flowDiffeomorph φ (-s) :=
  Diffeomorph.ext fun _ ↦ (rfl)

/-- Composing the time-`s` and time-`r` maps of the suspension flow gives its time-`(r + s)`
map. -/
@[simp]
theorem flowDiffeomorph_trans (s r : ℝ) :
    (flowDiffeomorph φ s).trans (flowDiffeomorph φ r) = flowDiffeomorph φ (r + s) :=
  Diffeomorph.ext fun z ↦ ((flow φ).map_add r s z).symm

end Manifold

/-! ### Comparison with the topological mapping torus -/

/-- The smooth mapping torus of `φ` is homeomorphic to Tau Ceti's topological mapping torus
`TauCeti.MappingTorus` of `φ⁻¹`, by `[t, x] ↦ [x, t]`. -/
def homeomorphMappingTorus : SmoothMappingTorus φ ≃ₜ MappingTorus φ.toHomeomorph.symm where
  toFun := MulAction.orbitRelQuotientLift
    (fun z ↦ MappingTorus.mk _ ((ofProd φ).symm z).2 ((ofProd φ).symm z).1) fun k z ↦ by
      rw [ofProd_symm_smul, ← Diffeomorph.toHomeomorph_symm_zpow_apply]
      exact MappingTorus.mk_vadd _ _ _ _
  invFun := MappingTorus.lift _ (fun p ↦ mk φ p.2 p.1) fun k x t ↦ by
    rw [Diffeomorph.toHomeomorph_symm_zpow_apply, mk_add_intCast]
    simp
  left_inv z := by
    obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    simp [mk, MulAction.orbitRelQuotientLift_mk]
  right_inv w := by
    obtain ⟨⟨x, t⟩, rfl⟩ := MappingTorus.mk_surjective _ w
    simp [mk, MulAction.orbitRelQuotientLift_mk]
  continuous_toFun := continuous_orbitRelQuotientLift_iff.2 <|
    (MappingTorus.continuous_mk _).comp
      ((continuous_ofProd_symm φ).snd.prodMk (continuous_ofProd_symm φ).fst)
  continuous_invFun := MappingTorus.continuous_lift _ _ <|
    (continuous_uncurry_mk φ).comp continuous_swap

/-- The homeomorphism with the topological mapping torus sends `[t, x]` to `[x, t]`. -/
@[simp]
theorem homeomorphMappingTorus_mk (t : ℝ) (x : M) :
    homeomorphMappingTorus φ (mk φ t x) = MappingTorus.mk _ x t :=
  MulAction.orbitRelQuotientLift_mk _

/-- The inverse of the homeomorphism with the topological mapping torus sends `[x, t]` to
`[t, x]`. -/
@[simp]
theorem homeomorphMappingTorus_symm_mk (x : M) (t : ℝ) :
    (homeomorphMappingTorus φ).symm (MappingTorus.mk _ x t) = mk φ t x :=
  MappingTorus.lift_mk _ _ _ x t

/-- The homeomorphism with the topological mapping torus lies over the circle. -/
@[simp]
theorem proj_homeomorphMappingTorus (z : SmoothMappingTorus φ) :
    MappingTorus.proj _ (homeomorphMappingTorus φ z) = proj φ z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

end SmoothMappingTorus

end TauCeti
