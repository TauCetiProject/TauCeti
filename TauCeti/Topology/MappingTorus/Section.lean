/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingTorus.Covering
public import TauCeti.Topology.MappingTorus.LocalProduct
public import TauCeti.Topology.MappingTorus.Refl
public import TauCeti.Topology.PathSpace.Seamed
import TauCeti.Algebra.AddCircle
import TauCeti.Topology.Instances.AddCircle.UnitInterval
import TauCeti.Topology.MappingSpace.FreeLoop

/-!
# Sections of a mapping torus and seamed paths

A point `z` of the mapping torus of `φ : F ≃ₜ F` lying over `(t : UnitAddCircle)` has a unique
representative `mk φ x t` at height `t` (`TauCeti.MappingTorus.existsUnique_mk_eq`). Its fibre
coordinate `x = TauCeti.MappingTorus.fiberCoord φ z t` depends continuously on the pair `(z, t)`
(`TauCeti.MappingTorus.continuousOn_fiberCoord`), because over an interval of heights of length one
the mapping torus is a product.

A `φ`-seamed path `γ`, with `γ 1 = φ (γ 0)`, traces the section `t ↦ mk φ (γ t) t` of the
projection of the mapping torus to the circle: the seam is exactly the identification of
`(γ 0, 0)` with `(φ (γ 0), 1)`. Conversely the fibre coordinates of a section form a seamed path.
This identifies the seamed path space with the space of sections, as topological spaces
(`TauCeti.SeamedPath.sectionHomeomorph`). Through it, a loop of seamed paths is a loop of
sections, which sweeps a torus in the mapping torus rather than in `F`.

More generally, a family of sections `s : K × UnitAddCircle → MappingTorus φ`, with `s (k, θ)`
over `θ`, sweeps the mapping torus of the identity of `K`, which is `K × UnitAddCircle`
(`TauCeti.MappingTorus.reflHomeomorph`), into the mapping torus of `φ`. Read on the infinite
cyclic covers, through the fibre coordinates, it is the map of cylinders
`TauCeti.MappingTorus.sectionCylinderMap`, `(k, t) ↦ (x, t)` with `mk φ x t = s (k, t)`. Since the
fibre coordinate one sheet up is the image under `φ` (`TauCeti.MappingTorus.fiberCoord_add_one`),
this map intertwines the deck transformations, and the swept map is the map of mapping tori
descended from it (`TauCeti.MappingTorus.descend_sectionCylinderMap`). A family of seamed paths
`ℓ : K → SeamedPath φ` is such a family of sections (`TauCeti.SeamedPath.sectionFamily`).

## Main definitions

* `TauCeti.MappingTorus.fiberCoord φ z t`: the fibre coordinate at height `t` of a point `z` over
  `(t : UnitAddCircle)`.
* `TauCeti.SeamedPath.sectionHomeomorph φ`: the homeomorphism from the `φ`-seamed paths to the
  continuous sections of the projection `MappingTorus φ → UnitAddCircle`.
* `TauCeti.MappingTorus.sectionCylinderMap φ s hs`: a family of sections, read on the cylinders.
* `TauCeti.SeamedPath.sectionFamily φ ℓ`: the family of sections of a family of seamed paths.

## References

* S. Dostoglou and D. A. Salamon, *Self-dual instantons and holomorphic curves*, Ann. of Math. 139
  (1994), 581–640.
-/

public section

noncomputable section

open Set Topology unitInterval Function

namespace TauCeti

variable {F : Type*} [TopologicalSpace F] (φ : F ≃ₜ F)

namespace MappingTorus

/-- Shifting a representative at height `s` to a height `t` with the same image in the circle. -/
private theorem mk_zpow_round_sub {s t : ℝ} (h : (s : UnitAddCircle) = t) (x : F) :
    mk φ ((φ ^ round (t - s)) x) t = mk φ x s := by
  obtain ⟨n, hn⟩ := AddCircle.coe_eq_coe_iff_exists_zsmul.1 h.symm
  replace hn : s + n = t := by rw [zsmul_eq_mul, mul_one] at hn; linarith
  rw [← hn, add_sub_cancel_left, round_intCast, mk_vadd]

/-- **A point over `(t : UnitAddCircle)` has a unique representative at height `t`.** -/
theorem existsUnique_mk_eq {z : MappingTorus φ} {t : ℝ} (h : proj φ z = t) :
    ∃! x, mk φ x t = z := by
  obtain ⟨⟨y, s⟩, rfl⟩ := mk_surjective φ z
  rw [proj_mk] at h
  refine ⟨(φ ^ round (t - s)) y, mk_zpow_round_sub φ h y, fun x hx ↦ ?_⟩
  obtain ⟨m, hm, hmt⟩ := (mk_eq_iff φ).1 hx
  rw [← hm, ← hmt, add_sub_cancel_left, round_intCast]

/-- The fibre coordinate at height `t` of a point `z` of the mapping torus: when `z` lies over
`(t : UnitAddCircle)`, the unique `x` with `mk φ x t = z` (`TauCeti.MappingTorus.mk_fiberCoord`).
Otherwise its value is not meaningful. -/
def fiberCoord (z : MappingTorus φ) (t : ℝ) : F :=
  (φ ^ round (t - (mk_surjective φ z).choose.2)) (mk_surjective φ z).choose.1

/-- The fibre coordinate of a point over `(t : UnitAddCircle)` represents it at height `t`. -/
theorem mk_fiberCoord {z : MappingTorus φ} {t : ℝ} (h : proj φ z = t) :
    mk φ (fiberCoord φ z t) t = z := by
  have hp : mk φ (mk_surjective φ z).choose.1 (mk_surjective φ z).choose.2 = z :=
    (mk_surjective φ z).choose_spec
  unfold fiberCoord
  generalize (mk_surjective φ z).choose = p at hp ⊢
  rw [← hp, proj_mk] at h
  rw [mk_zpow_round_sub φ h, hp]

/-- The fibre coordinate at height `t` of the point `mk φ x t` is `x`. -/
@[simp]
theorem fiberCoord_mk (x : F) (t : ℝ) : fiberCoord φ (mk φ x t) t = x :=
  (existsUnique_mk_eq φ (proj_mk φ x t)).unique (mk_fiberCoord φ (proj_mk φ x t)) rfl

/-- The fibre coordinate of a point over `(t : UnitAddCircle)` is characterized by representing
it at height `t`. -/
theorem fiberCoord_eq_iff {z : MappingTorus φ} {t : ℝ} (h : proj φ z = t) {x : F} :
    fiberCoord φ z t = x ↔ mk φ x t = z where
  mp hx := hx ▸ mk_fiberCoord φ h
  mpr hx := hx ▸ fiberCoord_mk φ x t

/-- **The fibre coordinate is continuous** on the pairs `(z, t)` with `z` over
`(t : UnitAddCircle)`. Near such a pair the mapping torus is the product of `F` with an interval of
heights of length one (`TauCeti.MappingTorus.isOpenEmbedding_mk_Ioo`), and the fibre coordinate is
the first coordinate of the inverse chart. -/
theorem continuousOn_fiberCoord :
    ContinuousOn (fun p : MappingTorus φ × ℝ ↦ fiberCoord φ p.1 p.2)
      {p | proj φ p.1 = p.2} := by
  rintro ⟨z₀, t₀⟩ (h₀ : proj φ z₀ = t₀)
  set a : ℝ := t₀ - 1 / 2 with ha_def
  have ha : t₀ ∈ Ioo a (a + 1) := ⟨by linarith, by linarith⟩
  have : Nonempty (F × Ioo a (a + 1)) := ⟨(fiberCoord φ z₀ t₀, ⟨t₀, ha⟩)⟩
  let e := (isOpenEmbedding_mk_Ioo φ a).toOpenPartialHomeomorph
  have he : ∀ {z : MappingTorus φ} {t : ℝ} (ht : t ∈ Ioo a (a + 1)), proj φ z = t →
      e.symm z = (fiberCoord φ z t, ⟨t, ht⟩) := fun ht h ↦ by
    conv_lhs => rw [← mk_fiberCoord φ h]
    exact (isOpenEmbedding_mk_Ioo φ a).toOpenPartialHomeomorph_left_inv
      (x := (fiberCoord φ _ _, ⟨_, ht⟩))
  have hz₀ : z₀ ∈ e.target := by
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨(fiberCoord φ z₀ t₀, ⟨t₀, ha⟩), mk_fiberCoord φ h₀⟩
  have hcont : ContinuousAt (fun p : MappingTorus φ × ℝ ↦ (e.symm p.1).1) (z₀, t₀) :=
    continuous_fst.continuousAt.comp ((e.continuousAt_symm hz₀).comp continuous_fst.continuousAt)
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (by simp [he ha h₀])
  have hIoo : ∀ᶠ p : MappingTorus φ × ℝ in 𝓝[{p | proj φ p.1 = p.2}] (z₀, t₀),
      p.2 ∈ Ioo a (a + 1) :=
    nhdsWithin_le_nhds (continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ha))
  filter_upwards [hIoo, self_mem_nhdsWithin] with p hp hpS
  simp [he hp hpS]

/-- The fibre coordinate one sheet up is the image under the monodromy:
`fiberCoord φ z (t + 1) = φ (fiberCoord φ z t)` for `z` over `(t : UnitAddCircle)`. -/
theorem fiberCoord_add_one {z : MappingTorus φ} {t : ℝ} (h : proj φ z = t) :
    fiberCoord φ z (t + 1) = φ (fiberCoord φ z t) :=
  (fiberCoord_eq_iff φ (h.trans (AddCircle.coe_add_period 1 t).symm)).2
    ((mk_apply_add_one φ _ t).trans (mk_fiberCoord φ h))

section SectionFamily

variable {K : Type*} [TopologicalSpace K] (s : C(K × UnitAddCircle, MappingTorus φ))
  (hs : ∀ k θ, proj φ (s (k, θ)) = θ)

/-- **A family of sections, read on the cylinders.** For a family of sections
`s : K × UnitAddCircle → MappingTorus φ`, with `s (k, θ)` over `θ`, the map of cylinders
`(k, t) ↦ (x, t)`, where `x` is the fibre coordinate of `s (k, t)` at height `t`. -/
def sectionCylinderMap : C(K × ℝ, F × ℝ) where
  toFun p := (fiberCoord φ (s (p.1, p.2)) p.2, p.2)
  continuous_toFun := ((continuousOn_fiberCoord φ).comp_continuous
    ((s.continuous.comp (continuous_fst.prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))).prodMk continuous_snd)
    fun p ↦ hs p.1 p.2).prodMk continuous_snd

@[simp]
theorem sectionCylinderMap_apply (p : K × ℝ) :
    sectionCylinderMap φ s hs p = (fiberCoord φ (s (p.1, p.2)) p.2, p.2) :=
  (rfl)

/-- A family of sections, read on the cylinders, intertwines the deck transformation of the
identity of `K` with that of `φ`: one sheet up, the fibre coordinate is moved by `φ`. -/
theorem semiconj_sectionCylinderMap_deck :
    Function.Semiconj (sectionCylinderMap φ s hs) (deck (Homeomorph.refl K)) (deck φ) :=
  fun p ↦ by
    simp only [sectionCylinderMap_apply, deck_apply, Homeomorph.refl_apply, id_eq,
      AddCircle.coe_add_period, fiberCoord_add_one φ (hs _ _)]

/-- **The swept map of a family of sections descends from the cylinders.** The map of mapping tori
descended from `sectionCylinderMap φ s hs` is `s`, read on the mapping torus of the identity of
`K` through `MappingTorus.reflHomeomorph`. -/
theorem descend_sectionCylinderMap :
    descend (Homeomorph.refl K) φ (sectionCylinderMap φ s hs)
        (semiconj_sectionCylinderMap_deck φ s hs) =
      s.comp (reflHomeomorph (F := K) :
        C(MappingTorus (Homeomorph.refl K), K × UnitAddCircle)) := by
  ext z
  obtain ⟨⟨k, t⟩, rfl⟩ := mk_surjective _ z
  rw [descend_mk, sectionCylinderMap_apply, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
    reflHomeomorph_mk]
  exact mk_fiberCoord φ (hs _ _)

end SectionFamily

end MappingTorus

namespace SeamedPath

open MappingTorus

/-- The seam of a mapping torus, at the two ends of the unit interval. -/
private theorem mk_apply_coe_one (x : F) : mk φ (φ x) ((1 : I) : ℝ) = mk φ x ((0 : I) : ℝ) := by
  rw [(by simp : ((1 : I) : ℝ) = ((0 : I) : ℝ) + 1), mk_apply_add_one]

/-- The curve in the mapping torus traced by a seamed path, before passing to the circle. -/
private def sweep (γ : SeamedPath φ) : C(I, MappingTorus φ) :=
  ⟨fun t ↦ mk φ (γ.val t) t, (continuous_mk φ).comp (γ.val.continuous.prodMk continuous_subtypeVal)⟩

@[simp]
private theorem sweep_apply (γ : SeamedPath φ) (t : I) : sweep φ γ t = mk φ (γ.val t) t :=
  (rfl)

private theorem continuous_sweep : Continuous (sweep φ) :=
  ContinuousMap.continuous_of_continuous_uncurry _ <|
    (continuous_mk φ).comp (continuous_eval.prodMk (continuous_subtypeVal.comp continuous_snd))
      |>.comp ((continuous_subtypeVal.prodMap continuous_id))

/-- The curve traced by a seamed path closes up: the seam identifies its two ends. -/
private theorem sweep_zero_eq_one (γ : SeamedPath φ) : sweep φ γ 0 = sweep φ γ 1 := by
  rw [sweep_apply, sweep_apply, apply_one, mk_apply_coe_one]

private theorem proj_sweep (γ : SeamedPath φ) (t : I) :
    proj φ (sweep φ γ t) = ((t : ℝ) : UnitAddCircle) :=
  proj_mk φ _ _

/-- The closed curves of the unit interval in the mapping torus lying over the circle. -/
private abbrev Sweep :=
  {g : ClosedUnitPath (MappingTorus φ) // ∀ t, proj φ (g.val t) = ((t : ℝ) : UnitAddCircle)}

/-- The fibre coordinates of a closed curve lying over the circle. -/
private def unsweep (g : Sweep φ) : C(I, F) :=
  ⟨fun t ↦ fiberCoord φ (g.val.val t) t,
    (continuousOn_fiberCoord φ).comp_continuous (g.val.val.continuous.prodMk continuous_subtypeVal)
      g.property⟩

private theorem unsweep_apply (g : Sweep φ) (t : I) :
    unsweep φ g t = fiberCoord φ (g.val.val t) t :=
  (rfl)

private theorem continuous_unsweep : Continuous (unsweep φ) :=
  ContinuousMap.continuous_of_continuous_uncurry _ <|
    (continuousOn_fiberCoord φ).comp_continuous
      ((continuous_eval.comp ((continuous_subtypeVal.comp continuous_subtypeVal).prodMap
        continuous_id)).prodMk (continuous_subtypeVal.comp continuous_snd))
      fun p ↦ p.1.property p.2

/-- The fibre coordinates of a closed curve over the circle form a seamed path. -/
private theorem unsweep_one (g : Sweep φ) : unsweep φ g 1 = φ (unsweep φ g 0) := by
  have h0 : mk φ (unsweep φ g 0) ((0 : I) : ℝ) = g.val.val 0 :=
    mk_fiberCoord φ (g.property 0)
  have h1 : g.val.val 1 = mk φ (φ (unsweep φ g 0)) ((1 : I) : ℝ) := by
    rw [← g.val.property, ← h0, mk_apply_coe_one]
  rw [unsweep_apply, h1, fiberCoord_mk]

/-- Seamed paths are the closed curves of the unit interval lying over the circle. -/
private def sweepHomeomorph : SeamedPath φ ≃ₜ Sweep φ where
  toFun γ := ⟨⟨sweep φ γ, sweep_zero_eq_one φ γ⟩, proj_sweep φ γ⟩
  invFun g := ⟨unsweep φ g, unsweep_one φ g⟩
  left_inv γ := ext fun t ↦ fiberCoord_mk φ (γ.val t) t
  right_inv g := Subtype.ext <| Subtype.ext <| ContinuousMap.ext fun t ↦
    mk_fiberCoord φ (g.property t)
  continuous_toFun := ((continuous_sweep φ).subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_unsweep φ).subtype_mk _

@[simp]
private theorem sweepHomeomorph_apply (γ : SeamedPath φ) (t : I) :
    (sweepHomeomorph φ γ).val.val t = sweep φ γ t :=
  (rfl)

/-- **Seamed paths are sections of the mapping torus.** A `φ`-seamed path `γ` gives the section
`(t : UnitAddCircle) ↦ mk φ (γ t) t` of the projection of the mapping torus to the circle, and
every continuous section arises from a unique seamed path, its fibre coordinates. -/
def sectionHomeomorph :
    SeamedPath φ ≃ₜ {s : C(UnitAddCircle, MappingTorus φ) // ∀ θ, proj φ (s θ) = θ} :=
  (sweepHomeomorph φ).trans
    (Homeomorph.subtype unitAddCircleMapHomeomorphClosedUnitPath fun s ↦ by
      simp only [unitAddCircleMapHomeomorphClosedUnitPath_apply]
      exact ⟨fun h t ↦ h _, fun h θ ↦ by
        obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval (p := 1) θ
        simpa using h t⟩).symm

/-- The section of a seamed path passes through `mk φ (γ t) t` at time `t`. -/
@[simp]
theorem sectionHomeomorph_apply (γ : SeamedPath φ) (t : I) :
    (sectionHomeomorph φ γ).val (t : ℝ) = mk φ (γ.val t) t := by
  simp [sectionHomeomorph]

/-- The section of a seamed path is a section: it lies over `θ` at every `θ`. -/
@[simp]
theorem proj_sectionHomeomorph_apply (γ : SeamedPath φ) (θ : UnitAddCircle) :
    proj φ ((sectionHomeomorph φ γ).val θ) = θ :=
  (sectionHomeomorph φ γ).property θ

/-- The seamed path of a section consists of the fibre coordinates of the section. -/
@[simp]
theorem sectionHomeomorph_symm_apply
    (s : {s : C(UnitAddCircle, MappingTorus φ) // ∀ θ, proj φ (s θ) = θ}) (t : I) :
    ((sectionHomeomorph φ).symm s).val t = fiberCoord φ (s.val t) t := by
  conv_rhs => rw [← (sectionHomeomorph φ).apply_symm_apply s]
  rw [sectionHomeomorph_apply, fiberCoord_mk]

/-- The seamed path of a section represents the section at every time. -/
theorem mk_sectionHomeomorph_symm_apply
    (s : {s : C(UnitAddCircle, MappingTorus φ) // ∀ θ, proj φ (s θ) = θ}) (t : I) :
    mk φ (((sectionHomeomorph φ).symm s).val t) t = s.val t := by
  rw [sectionHomeomorph_symm_apply]
  exact mk_fiberCoord φ (s.property _)

section SectionFamily

variable {K : Type*} [TopologicalSpace K]

/-- **The family of sections of a family of seamed paths.** For `ℓ : K → SeamedPath φ`, the map
`(k, θ) ↦ s_k θ`, where `s_k` is the section of the mapping torus traced by `ℓ k`
(`TauCeti.SeamedPath.sectionHomeomorph`). -/
def sectionFamily (ℓ : C(K, SeamedPath φ)) : C(K × UnitAddCircle, MappingTorus φ) :=
  ContinuousMap.uncurry
    ⟨fun k ↦ (sectionHomeomorph φ (ℓ k)).val,
      continuous_subtypeVal.comp ((sectionHomeomorph φ).continuous.comp ℓ.continuous)⟩

@[simp]
theorem sectionFamily_apply (ℓ : C(K, SeamedPath φ)) (k : K) (θ : UnitAddCircle) :
    sectionFamily φ ℓ (k, θ) = (sectionHomeomorph φ (ℓ k)).val θ :=
  (rfl)

/-- The family of sections of a family of seamed paths consists of sections. -/
theorem proj_sectionFamily (ℓ : C(K, SeamedPath φ)) (k : K) (θ : UnitAddCircle) :
    proj φ (sectionFamily φ ℓ (k, θ)) = θ :=
  (sectionHomeomorph φ (ℓ k)).property θ

/-- At height zero, the family of sections of a family of seamed paths passes through the start
points of the paths. -/
theorem sectionFamily_zero (ℓ : C(K, SeamedPath φ)) (k : K) :
    sectionFamily φ ℓ (k, 0) = mk φ ((ℓ k).val 0) 0 := by
  simpa using sectionHomeomorph_apply φ (ℓ k) 0

end SectionFamily

end SeamedPath

end TauCeti
