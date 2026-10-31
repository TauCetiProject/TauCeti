/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra
public import TauCeti.RingTheory.Dagger.Noetherian

/-!
# Fringe presentations of dagger algebras

A dagger algebra `A = W_n ⧸ I` is a quotient of the Monsky–Washnitzer algebra
`W_n = K⟨X₁, …, Xₙ⟩† = ⋃_{ρ > 1} T_n(ρ)`, where `T_n(ρ)` is the algebra of series restricted at the
constant radius `ρ`. A *fringe presentation* records relations `f₁, …, f_r` generating `I`
which all converge on one polydisc of radius `ρ₀ > 1`, together with an isomorphism
`W_n ⧸ (f₁, …, f_r) ≃ₐ[K] A`. For `1 < ρ ≤ ρ₀` it has the *stage*

```text
A_ρ = T_n(ρ) ⧸ (f₁, …, f_r) T_n(ρ),
```

the algebra of functions on the closed subspace of the polydisc of radius `ρ` cut out by the
relations. Shrinking the radius gives transition maps `A_ρ' → A_ρ` for `ρ ≤ ρ'`, and the
inclusions `T_n(ρ) ⊆ W_n` give compatible maps `A_ρ → A`. The images of these maps are the
*fringe algebras* `B_ρ ⊆ A`; the maps `A_ρ → A` need not be injective.

The main result is that `A` is the colimit of its stages as `ρ → 1⁺`. Every element of `A`
comes from a stage (`exists_mem_fringeAlgebra`), and an element of a stage which vanishes in `A`
already vanishes in some smaller stage (`exists_stageMap_eq_zero`): a relation in `W_n` has only
finitely many overconvergent coefficients, so it already holds at some radius `ρ > 1`. Hence
compatible families of maps out of the stages factor uniquely through `A` (`lift`, `lift_ofStage`
and `algHom_ext`). Every dagger algebra over a complete field has a fringe presentation, since
the ideal of a presentation is finitely generated (`IsDaggerAlgebra.nonempty_fringePresentation`).

This presents a dagger algebra through a decreasing family of algebras of functions on closed
neighbourhoods `Sp(A_ρ)` of the affinoid space of its completion. Grosse-Klönne takes the outer
radius in the divisible hull `√|K^×|` of the value group, so that the stages at such radii are
affinoid; the colimit statements do not need this, and over a nontrivially normed field such
radii are arbitrarily close to `1`.

## Main definitions

* `TauCeti.Dagger.FringePresentation K A`: a fringe presentation of the `K`-algebra `A`.
* `TauCeti.Dagger.FringePresentation.stage`: the stage `A_ρ`, for `ρ ∈ (1, ρ₀]`.
* `TauCeti.Dagger.FringePresentation.stageMap`: the transition map `A_ρ' → A_ρ` for `ρ ≤ ρ'`.
* `TauCeti.Dagger.FringePresentation.ofStage`: the map `A_ρ → A`.
* `TauCeti.Dagger.FringePresentation.fringeAlgebra`: the fringe algebra `B_ρ`, the image of
  `A_ρ` in `A`.
* `TauCeti.Dagger.FringePresentation.lift`: the map out of `A` induced by a compatible family of
  maps out of the stages.

## Main results

* `TauCeti.Dagger.FringePresentation.exists_mem_fringeAlgebra`: `A` is the union of its fringe
  algebras, which decrease with the radius (`fringeAlgebra_antitone`).
* `TauCeti.Dagger.FringePresentation.exists_stageMap_eq_zero`: the kernel of `A_ρ → A` is the
  union of the kernels of the transition maps to smaller stages.
* `TauCeti.Dagger.FringePresentation.lift_ofStage` and
  `TauCeti.Dagger.FringePresentation.algHom_ext`: the universal property of `A` as the colimit of
  its stages in `K`-algebras.
* `TauCeti.Dagger.IsDaggerAlgebra.nonempty_fringePresentation`: every dagger algebra over a
  complete field has a fringe presentation.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Lemma 1.8.
* A. Vezzani, *The Monsky–Washnitzer and the overconvergent realizations*, Int. Math. Res. Not.
  IMRN 2018, Appendix A, Proposition A.22.
-/

public section

namespace TauCeti.Dagger

open Filter Topology _root_.MvPowerSeries
open TauCeti.MvPowerSeries (isRestricted_of_le restrictedRadiusHom restrictedRadiusAlgHom
  restrictedRadiusAlgHom_apply)

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A]

/-- A **fringe presentation** of a `K`-algebra `A`: relations `f₁, …, f_r` in `n` variables, all
restricted at one radius `ρ₀ > 1`, together with an isomorphism from the quotient of the
Monsky–Washnitzer algebra `W_n` by the ideal they generate onto `A`. -/
structure FringePresentation where
  /-- The number of variables. -/
  n : ℕ
  /-- The outer radius `ρ₀`, at which every relation is restricted. -/
  radius : ℝ
  one_lt_radius : 1 < radius
  /-- The number of relations. -/
  r : ℕ
  /-- The relations, as series restricted at the outer radius. -/
  relation : Fin r → IsRestricted.subring (R := K) (fun _ : Fin n ↦ radius)
  /-- The identification of `W_n ⧸ (f₁, …, f_r)` with `A`. -/
  equiv : (washnitzerAlgebra (Fin n) K ⧸ Ideal.span (Set.range fun i ↦
    washnitzerAlgebra.ofRestricted one_lt_radius (fun _ ↦ le_rfl) (relation i))) ≃ₐ[K] A

namespace FringePresentation

variable {K A} (P : FringePresentation K A)

/-- The ideal `(f₁, …, f_r)` of `W_n` generated by the relations. It is reducible, so that it
can be used interchangeably with the ideal in the type of `FringePresentation.equiv`. -/
noncomputable abbrev ideal : Ideal (washnitzerAlgebra (Fin P.n) K) :=
  Ideal.span (Set.range fun i ↦
    washnitzerAlgebra.ofRestricted P.one_lt_radius (fun _ ↦ le_rfl) (P.relation i))

/-- The presentation `W_n ↠ A` underlying a fringe presentation. -/
noncomputable def proj : washnitzerAlgebra (Fin P.n) K →ₐ[K] A :=
  P.equiv.toAlgHom.comp (Ideal.Quotient.mkₐ K P.ideal)

theorem proj_surjective : Function.Surjective P.proj :=
  P.equiv.surjective.comp (Ideal.Quotient.mkₐ_surjective K _)

/-- The kernel of the presentation is the ideal generated by the relations. -/
theorem ker_proj : RingHom.ker P.proj = P.ideal := by
  ext f
  rw [RingHom.mem_ker, proj, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

/-- The ideal `(f₁, …, f_r) T_n(ρ)` generated by the relations at a radius `ρ ∈ (1, ρ₀]`. -/
noncomputable def stageIdeal (ρ : Set.Ioc (1 : ℝ) P.radius) :
    Ideal (IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ : ℝ))) :=
  Ideal.span (Set.range fun i ↦ restrictedRadiusHom (fun _ ↦ zero_le_one.trans ρ.2.1.le)
    (fun _ ↦ ρ.2.2) (P.relation i))

theorem stageIdeal_def (ρ : Set.Ioc (1 : ℝ) P.radius) :
    P.stageIdeal ρ = Ideal.span (Set.range fun i ↦
      restrictedRadiusHom (fun _ ↦ zero_le_one.trans ρ.2.1.le) (fun _ ↦ ρ.2.2) (P.relation i)) :=
  (rfl)

/-- The **stage** `A_ρ = T_n(ρ) ⧸ (f₁, …, f_r)` of a fringe presentation at a radius
`ρ ∈ (1, ρ₀]`. -/
abbrev stage (ρ : Set.Ioc (1 : ℝ) P.radius) : Type _ :=
  IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ : ℝ)) ⧸ P.stageIdeal ρ

/-- Restriction to a smaller radius maps relations to relations. -/
private theorem stageIdeal_le_comap {ρ ρ' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ') :
    P.stageIdeal ρ' ≤ (P.stageIdeal ρ).comap
      (restrictedRadiusAlgHom (R := K) (fun _ ↦ zero_le_one.trans ρ.2.1.le) fun _ ↦ h) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact Ideal.subset_span ⟨i, Subtype.ext (by simp)⟩

/-- The **transition map** `A_ρ' → A_ρ` of a fringe presentation for radii `ρ ≤ ρ'`, induced by
restricting series to the smaller radius. -/
noncomputable def stageMap {ρ ρ' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ') :
    P.stage ρ' →ₐ[K] P.stage ρ :=
  Ideal.quotientMapₐ _ _ (P.stageIdeal_le_comap h)

@[simp]
theorem stageMap_mk {ρ ρ' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ')
    (f : IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ' : ℝ))) :
    P.stageMap h (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _
      (restrictedRadiusHom (fun _ ↦ zero_le_one.trans ρ.2.1.le) (fun _ ↦ h) f) := by
  rw [stageMap, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, restrictedRadiusAlgHom_apply]

/-- The transition map from a stage to itself is the identity. -/
@[simp]
theorem stageMap_refl (ρ : Set.Ioc (1 : ℝ) P.radius) : P.stageMap (le_refl ρ) = AlgHom.id K _ := by
  ext x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [stageMap_mk, AlgHom.coe_id, id_eq]
  exact congrArg _ (Subtype.ext (by simp))

/-- Transition maps compose. -/
@[simp]
theorem stageMap_stageMap {ρ ρ' ρ'' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ') (h' : ρ' ≤ ρ'')
    (x : P.stage ρ'') : P.stageMap h (P.stageMap h' x) = P.stageMap (h.trans h') x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [stageMap_mk]
  exact congrArg _ (Subtype.ext (by simp))

/-- Transition maps compose, as an equality of bundled maps. -/
@[simp]
theorem stageMap_comp {ρ ρ' ρ'' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ') (h' : ρ' ≤ ρ'') :
    (P.stageMap h).comp (P.stageMap h') = P.stageMap (h.trans h') :=
  AlgHom.ext (P.stageMap_stageMap h h')

/-- The inclusion `T_n(ρ) ⊆ W_n` for `ρ > 1` followed by the presentation `W_n ↠ A`. -/
private noncomputable def restrictedToAlgebra (ρ : Set.Ioc (1 : ℝ) P.radius) :
    IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ : ℝ)) →ₐ[K] A where
  toRingHom := P.proj.toRingHom.comp (washnitzerAlgebra.ofRestricted ρ.2.1 fun _ ↦ le_rfl)
  commutes' a := by
    have : washnitzerAlgebra.ofRestricted ρ.2.1 (fun _ ↦ le_rfl) (algebraMap K _ a) =
        algebraMap K (washnitzerAlgebra (Fin P.n) K) a :=
      Subtype.ext (by simp [MvPowerSeries.algebraMap_apply])
    simp [this]

private theorem restrictedToAlgebra_apply (ρ : Set.Ioc (1 : ℝ) P.radius)
    (f : IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ : ℝ))) :
    P.restrictedToAlgebra ρ f = P.proj (washnitzerAlgebra.ofRestricted ρ.2.1 (fun _ ↦ le_rfl) f) :=
  (rfl)

private theorem stageIdeal_le_ker (ρ : Set.Ioc (1 : ℝ) P.radius) (f) (hf : f ∈ P.stageIdeal ρ) :
    P.restrictedToAlgebra ρ f = 0 := by
  refine (Submodule.span_le (p := RingHom.ker (P.restrictedToAlgebra ρ))).mpr ?_ hf
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, restrictedToAlgebra_apply, ← RingHom.mem_ker, ker_proj]
  exact Ideal.subset_span ⟨i, Subtype.ext (by simp)⟩

/-- The map `A_ρ → A` from a stage of a fringe presentation, induced by the inclusion
`T_n(ρ) ⊆ W_n`. -/
noncomputable def ofStage (ρ : Set.Ioc (1 : ℝ) P.radius) : P.stage ρ →ₐ[K] A :=
  Ideal.Quotient.liftₐ _ (P.restrictedToAlgebra ρ) (P.stageIdeal_le_ker ρ)

@[simp]
theorem ofStage_mk (ρ : Set.Ioc (1 : ℝ) P.radius)
    (f : IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ (ρ : ℝ))) :
    P.ofStage ρ (Ideal.Quotient.mk _ f) =
      P.proj (washnitzerAlgebra.ofRestricted ρ.2.1 (fun _ ↦ le_rfl) f) :=
  (rfl)

/-- The maps from the stages to `A` are compatible with the transition maps. -/
@[simp]
theorem ofStage_stageMap {ρ ρ' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ') (x : P.stage ρ') :
    P.ofStage ρ (P.stageMap h x) = P.ofStage ρ' x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [stageMap_mk, ofStage_mk]
  exact congrArg _ (Subtype.ext (by simp))

/-- The maps from the stages to `A` are compatible with the transition maps, as an equality of
bundled maps. -/
@[simp]
theorem ofStage_comp_stageMap {ρ ρ' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ') :
    (P.ofStage ρ).comp (P.stageMap h) = P.ofStage ρ' :=
  AlgHom.ext (P.ofStage_stageMap h)

/-- The **fringe algebra** `B_ρ ⊆ A` of a fringe presentation: the image of the stage `A_ρ`. -/
noncomputable def fringeAlgebra (ρ : Set.Ioc (1 : ℝ) P.radius) : Subalgebra K A :=
  (P.ofStage ρ).range

theorem mem_fringeAlgebra {ρ : Set.Ioc (1 : ℝ) P.radius} {a : A} :
    a ∈ P.fringeAlgebra ρ ↔ ∃ x, P.ofStage ρ x = a :=
  AlgHom.mem_range _

/-- Fringe algebras grow as the radius decreases. -/
theorem fringeAlgebra_antitone : Antitone P.fringeAlgebra := by
  intro ρ ρ' h a ha
  obtain ⟨x, rfl⟩ := P.mem_fringeAlgebra.mp ha
  exact P.mem_fringeAlgebra.mpr ⟨P.stageMap h x, P.ofStage_stageMap h x⟩

/-- An overconvergent series is restricted at some radius in `(1, ρ₀]`. -/
private theorem exists_isRestricted (f : washnitzerAlgebra (Fin P.n) K) :
    ∃ ρ : Set.Ioc (1 : ℝ) P.radius,
      IsRestricted (fun _ : Fin P.n ↦ (ρ : ℝ)) (f : MvPowerSeries (Fin P.n) K) := by
  obtain ⟨ρ, hf, hρ⟩ := ((eventually_isRestricted_of_mem_washnitzerAlgebra f.2).and
    (Ioc_mem_nhdsGT P.one_lt_radius)).exists
  exact ⟨⟨ρ, hρ⟩, hf⟩

/-- Every element of `A` lies in a fringe algebra: `A` is the union of its fringe algebras. -/
theorem exists_mem_fringeAlgebra (a : A) : ∃ ρ, a ∈ P.fringeAlgebra ρ := by
  obtain ⟨f, rfl⟩ := P.proj_surjective a
  obtain ⟨ρ, hρ⟩ := P.exists_isRestricted f
  refine ⟨ρ, P.mem_fringeAlgebra.mpr ⟨Ideal.Quotient.mk _ ⟨f, hρ⟩, ?_⟩⟩
  rw [ofStage_mk]
  exact congrArg P.proj (Subtype.ext (washnitzerAlgebra.coe_ofRestricted _ _ _))

/-- A series in the ideal of the relations lies in the ideal of the relations at every radius
`ρ > 1` close enough to `1`: its finitely many coefficients with respect to the relations are
overconvergent. -/
theorem eventually_mem_stageIdeal {f : washnitzerAlgebra (Fin P.n) K} (hf : f ∈ P.ideal) :
    ∀ᶠ ρ in 𝓝[>] (1 : ℝ), ∃ (hρ : ρ ∈ Set.Ioc 1 P.radius)
      (hfρ : IsRestricted (fun _ : Fin P.n ↦ ρ) (f : MvPowerSeries (Fin P.n) K)),
        ⟨f, hfρ⟩ ∈ P.stageIdeal ⟨ρ, hρ⟩ := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hf
  filter_upwards [eventually_all.mpr fun i ↦ eventually_isRestricted_of_mem_washnitzerAlgebra
    (c i).2, Ioc_mem_nhdsGT P.one_lt_radius] with ρ hcρ hρ
  let ρ' : Set.Ioc (1 : ℝ) P.radius := ⟨ρ, hρ⟩
  -- The same combination of the relations, computed at the radius `ρ`.
  let g : IsRestricted.subring (R := K) (fun _ : Fin P.n ↦ ρ) := ∑ i, ⟨c i, hcρ i⟩ *
    restrictedRadiusHom (fun _ ↦ zero_le_one.trans ρ'.2.1.le) (fun _ ↦ ρ'.2.2) (P.relation i)
  have hg : (g : MvPowerSeries (Fin P.n) K) = f := by
    rw [← hc]
    simp [g, washnitzerAlgebra.coe_ofRestricted]
  refine ⟨hρ, hg ▸ g.2, ?_⟩
  convert (show g ∈ P.stageIdeal ρ' from Ideal.sum_mem _ fun i _ ↦
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
  exact Subtype.ext hg.symm

/-- **The kernel of `A_ρ → A`.** An element of a stage which vanishes in `A` already vanishes in
some smaller stage. -/
theorem exists_stageMap_eq_zero {ρ : Set.Ioc (1 : ℝ) P.radius} (x : P.stage ρ)
    (hx : P.ofStage ρ x = 0) : ∃ (ρ' : Set.Ioc (1 : ℝ) P.radius) (h : ρ' ≤ ρ),
      P.stageMap h x = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [ofStage_mk, ← RingHom.mem_ker, ker_proj] at hx
  obtain ⟨ρ', ⟨hρ', ⟨hf, hmem⟩⟩, hle⟩ :=
    ((P.eventually_mem_stageIdeal hx).and (Ioc_mem_nhdsGT ρ.2.1)).exists
  refine ⟨⟨ρ', hρ'⟩, hle.2, ?_⟩
  rw [stageMap_mk, Ideal.Quotient.eq_zero_iff_mem]
  convert hmem using 1
  exact Subtype.ext (by simp)

section Lift

variable {B : Type*} [CommRing B] [Algebra K B] (φ : ∀ ρ, P.stage ρ →ₐ[K] B)
  (hφ : ∀ ρ ρ' (h : ρ ≤ ρ'), (φ ρ).comp (P.stageMap h) = φ ρ')

include hφ in
/-- A compatible family of maps out of the stages takes the same value on a series restricted at
two radii. -/
private theorem apply_mk_eq_of_le (f : washnitzerAlgebra (Fin P.n) K)
    {ρ ρ' : Set.Ioc (1 : ℝ) P.radius} (h : ρ ≤ ρ')
    (hρ : IsRestricted (fun _ : Fin P.n ↦ (ρ : ℝ)) (f : MvPowerSeries (Fin P.n) K))
    (hρ' : IsRestricted (fun _ : Fin P.n ↦ (ρ' : ℝ)) (f : MvPowerSeries (Fin P.n) K)) :
    φ ρ' (Ideal.Quotient.mk _ ⟨f, hρ'⟩) = φ ρ (Ideal.Quotient.mk _ ⟨f, hρ⟩) := by
  rw [← hφ ρ ρ' h, AlgHom.comp_apply, stageMap_mk]
  exact congrArg (fun x ↦ φ ρ (Ideal.Quotient.mk _ x)) (Subtype.ext (by simp))

include hφ in
private theorem apply_mk_eq (f : washnitzerAlgebra (Fin P.n) K)
    {ρ ρ' : Set.Ioc (1 : ℝ) P.radius}
    (hρ : IsRestricted (fun _ : Fin P.n ↦ (ρ : ℝ)) (f : MvPowerSeries (Fin P.n) K))
    (hρ' : IsRestricted (fun _ : Fin P.n ↦ (ρ' : ℝ)) (f : MvPowerSeries (Fin P.n) K)) :
    φ ρ (Ideal.Quotient.mk _ ⟨f, hρ⟩) = φ ρ' (Ideal.Quotient.mk _ ⟨f, hρ'⟩) := by
  have hmin : IsRestricted (fun _ : Fin P.n ↦ ((min ρ ρ' : Set.Ioc (1 : ℝ) P.radius) : ℝ))
      (f : MvPowerSeries (Fin P.n) K) := by
    rcases min_choice ρ ρ' with h | h <;> rw [h] <;> assumption
  rw [P.apply_mk_eq_of_le φ hφ f (min_le_left ρ ρ') hmin,
    P.apply_mk_eq_of_le φ hφ f (min_le_right ρ ρ') hmin]

/-- The value at an overconvergent series of the map induced on `W_n`, computed at a radius in
`(1, ρ₀]` at which the series is restricted. -/
private noncomputable def liftFun (f : washnitzerAlgebra (Fin P.n) K) : B :=
  φ (P.exists_isRestricted f).choose
    (Ideal.Quotient.mk _ ⟨f, (P.exists_isRestricted f).choose_spec⟩)

include hφ in
private theorem liftFun_eq (f : washnitzerAlgebra (Fin P.n) K) {ρ : Set.Ioc (1 : ℝ) P.radius}
    (hρ : IsRestricted (fun _ : Fin P.n ↦ (ρ : ℝ)) (f : MvPowerSeries (Fin P.n) K)) :
    P.liftFun φ f = φ ρ (Ideal.Quotient.mk _ ⟨f, hρ⟩) :=
  P.apply_mk_eq φ hφ f _ _

/-- The map `W_n → B` induced by a compatible family of maps out of the stages. -/
private noncomputable def liftWashnitzer : washnitzerAlgebra (Fin P.n) K →ₐ[K] B where
  toFun := P.liftFun φ
  map_one' := by
    obtain ⟨ρ, hρ⟩ := P.exists_isRestricted 1
    rw [P.liftFun_eq φ hφ 1 hρ, ← map_one (φ ρ), ← map_one (Ideal.Quotient.mk _)]
    exact congrArg (fun x ↦ φ ρ (Ideal.Quotient.mk _ x)) (Subtype.ext (by simp))
  map_mul' f g := by
    obtain ⟨ρ, hf⟩ := P.exists_isRestricted f
    obtain ⟨ρ', hg⟩ := P.exists_isRestricted g
    have hf' := isRestricted_of_le hf (fun _ ↦ zero_le_one.trans (min ρ ρ').2.1.le)
      fun _ ↦ min_le_left (ρ : ℝ) ρ'
    have hg' := isRestricted_of_le hg (fun _ ↦ zero_le_one.trans (min ρ ρ').2.1.le)
      fun _ ↦ min_le_right (ρ : ℝ) ρ'
    rw [P.liftFun_eq φ hφ (f * g) (ρ := min ρ ρ') (hf'.mul hg'), P.liftFun_eq φ hφ f hf',
      P.liftFun_eq φ hφ g hg', ← map_mul, ← map_mul]
    exact congrArg (fun x ↦ φ _ (Ideal.Quotient.mk _ x)) (Subtype.ext (by simp))
  map_zero' := by
    obtain ⟨ρ, hρ⟩ := P.exists_isRestricted 0
    rw [P.liftFun_eq φ hφ 0 hρ, ← map_zero (φ ρ), ← map_zero (Ideal.Quotient.mk _)]
    exact congrArg (fun x ↦ φ ρ (Ideal.Quotient.mk _ x)) (Subtype.ext (by simp))
  map_add' f g := by
    obtain ⟨ρ, hf⟩ := P.exists_isRestricted f
    obtain ⟨ρ', hg⟩ := P.exists_isRestricted g
    have hf' := isRestricted_of_le hf (fun _ ↦ zero_le_one.trans (min ρ ρ').2.1.le)
      fun _ ↦ min_le_left (ρ : ℝ) ρ'
    have hg' := isRestricted_of_le hg (fun _ ↦ zero_le_one.trans (min ρ ρ').2.1.le)
      fun _ ↦ min_le_right (ρ : ℝ) ρ'
    rw [P.liftFun_eq φ hφ (f + g) (ρ := min ρ ρ') (hf'.add hg'), P.liftFun_eq φ hφ f hf',
      P.liftFun_eq φ hφ g hg', ← map_add, ← map_add]
    exact congrArg (fun x ↦ φ _ (Ideal.Quotient.mk _ x)) (Subtype.ext (by simp))
  commutes' a := by
    obtain ⟨ρ, hρ⟩ := P.exists_isRestricted (algebraMap K _ a)
    rw [P.liftFun_eq φ hφ _ hρ, ← (φ ρ).commutes a, ← Ideal.Quotient.mk_algebraMap]
    congr 2

private theorem liftWashnitzer_apply (f : washnitzerAlgebra (Fin P.n) K) :
    P.liftWashnitzer φ hφ f = P.liftFun φ f :=
  (rfl)

private theorem liftWashnitzer_eq_zero (f : washnitzerAlgebra (Fin P.n) K) (hf : f ∈ P.ideal) :
    P.liftWashnitzer φ hφ f = 0 := by
  obtain ⟨ρ, hρ, hfρ, hmem⟩ := (P.eventually_mem_stageIdeal hf).exists
  rw [liftWashnitzer_apply, P.liftFun_eq φ hφ f (ρ := ⟨ρ, hρ⟩) hfρ,
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

/-- **The universal property of the colimit.** A family of maps out of the stages of a fringe
presentation, compatible with the transition maps, induces a map out of `A`. -/
noncomputable def lift : A →ₐ[K] B :=
  (Ideal.Quotient.liftₐ P.ideal (P.liftWashnitzer φ hφ) (P.liftWashnitzer_eq_zero φ hφ)).comp
    P.equiv.symm.toAlgHom

/-- The map induced by a compatible family `φ` recovers `φ ρ` on the image of each stage `A_ρ`:
`lift φ (ofStage ρ x) = φ ρ x`. -/
@[simp]
theorem lift_ofStage (ρ : Set.Ioc (1 : ℝ) P.radius) (x : P.stage ρ) :
    P.lift φ hφ (P.ofStage ρ x) = φ ρ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hf : IsRestricted (fun _ : Fin P.n ↦ (ρ : ℝ))
      (washnitzerAlgebra.ofRestricted ρ.2.1 (fun _ ↦ le_rfl) f : MvPowerSeries (Fin P.n) K) := by
    rw [washnitzerAlgebra.coe_ofRestricted]
    exact f.2
  simp only [lift, proj, ofStage_mk, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  rw [← AlgHom.comp_apply (Ideal.Quotient.liftₐ _ _ _), Ideal.Quotient.liftₐ_comp,
    liftWashnitzer_apply, P.liftFun_eq φ hφ _ hf]
  exact congrArg (fun x ↦ φ ρ (Ideal.Quotient.mk _ x)) (Subtype.ext (by simp))

/-- The map induced by a compatible family `φ`, composed with the map `A_ρ → A` from a stage,
recovers `φ ρ`. -/
@[simp]
theorem lift_comp_ofStage (ρ : Set.Ioc (1 : ℝ) P.radius) :
    (P.lift φ hφ).comp (P.ofStage ρ) = φ ρ :=
  AlgHom.ext (P.lift_ofStage φ hφ ρ)

end Lift

/-- Maps out of `A` are determined by their composites with the maps from the stages. Together
with `lift`, this exhibits `A` as the colimit of the stages in `K`-algebras. -/
theorem algHom_ext {B : Type*} [Semiring B] [Algebra K B] {f g : A →ₐ[K] B}
    (h : ∀ ρ, f.comp (P.ofStage ρ) = g.comp (P.ofStage ρ)) : f = g := by
  ext a
  obtain ⟨ρ, x, rfl⟩ := (P.exists_mem_fringeAlgebra a).imp fun _ ↦ P.mem_fringeAlgebra.mp
  exact DFunLike.congr_fun (h ρ) x

end FringePresentation

/-- **Existence of fringe presentations.** Every dagger algebra over a complete field has a fringe
presentation: the ideal of a presentation `W_n ↠ A` is finitely generated, and finitely many
overconvergent generators are restricted at a common radius `ρ₀ > 1`. -/
theorem IsDaggerAlgebra.nonempty_fringePresentation [CompleteSpace K] [IsDaggerAlgebra K A] :
    Nonempty (FringePresentation K A) := by
  obtain ⟨n, π, hπ⟩ := IsDaggerAlgebra.exists_surjective (K := K) (A := A)
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (RingHom.ker π))
  obtain ⟨ρ, hgρ, hρ⟩ := ((eventually_all.mpr fun i ↦
    eventually_isRestricted_of_mem_washnitzerAlgebra (g i).2).and self_mem_nhdsWithin).exists
  refine ⟨⟨n, ρ, hρ, r, fun i ↦ ⟨g i, hgρ i⟩, (Ideal.quotientEquivAlgOfEq K ?_).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ)⟩⟩
  rw [← hg]
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun i ↦ Subtype.ext (washnitzerAlgebra.coe_ofRestricted _ _ _)))

end TauCeti.Dagger
