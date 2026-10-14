/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.CoefficientMap
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.InflationRestriction

/-!
# Invariants descended along lifts to refinements

Let `φ : A → A'` be an equivariant map between the coefficient modules of two formations `F` and
`F'` on `G`, and let `σ` assign to every finite normal layer `L` a homomorphism
`σ_L : H²(L, A) → ℚ/ℤ` that does not change under inflation to a refinement of `L`. Suppose that

* every class of `H²(L, A')` becomes, after inflation to some refinement `L'` of `L`, the image
  under `φ` of a class of `H²(L', A)`, and
* `σ` vanishes on the classes that `φ` kills.

Then `σ` descends to an invariant `descendedInv φ σ … L : H²(L, A') → ℚ/ℤ` on every layer: the
invariant of a class is `σ` of a lift of an inflation of it, whichever refinement and lift are
chosen (`descendedInv_eq`). It is characterized by the two equations `descendedInv_map` (on the
image of `φ` it is `σ`) and `descendedInv_infl` (it does not change under inflation)
(`descendedInv_unique`). This is the shape of Tate's definition of the invariant map of idele
classes from the sum of the local invariants of ideles. That sum is defined on `H²(L, I_L)` and,
because it vanishes on the kernel of `H²(L, I_L) → H²(L, C_L)`, induces an invariant only on the
image of this map, which can be a proper subgroup: for the biquadratic field `ℚ(√13, √17)` the
image is killed by `2` while `H²(L, C_L)` is cyclic of order `4`. Classically, every class lifts
after inflation to a suitable cyclotomic refinement.

The invariant inherits the restriction and conjugation laws of `σ` (`descendedInv_res`,
`descendedInv_conj`), because restriction, conjugation and the maps induced by `φ` commute with
inflation. Suppose moreover that `H¹` of every layer of `F'` vanishes, that `σ` vanishes *exactly*
on the classes that `φ` kills, and that every layer `L`, of degree `n`, has a refinement carrying a
class with `σ = 1/n`. Then the invariant of `L` is injective with image the `n`-torsion of `ℚ/ℤ`,
and `F'` is a class formation with this invariant (`ClassFormation.ofDescendedInv`). Injectivity
holds because inflation is injective once `H¹` vanishes. The image of a class with `σ = 1/n` on a
refinement `L'` restricts to zero on the layer `L'/L`, where `σ` becomes `n • (1/n) = 0`, so by the
inflation-restriction sequence it is inflated from `L`.

## Main definitions

* `TauCeti.ClassFieldTheory.descendedInv`: the invariant of `F'` descended from `σ`.
* `TauCeti.ClassFieldTheory.ClassFormation.ofDescendedInv`: the class formation on `F'` with the
  descended invariant.

## Main statements

* `TauCeti.ClassFieldTheory.descendedInv_eq`: the invariant of a class is `σ` of any lift of any
  inflation of it.
* `TauCeti.ClassFieldTheory.descendedInv_map`, `TauCeti.ClassFieldTheory.descendedInv_infl` and
  `TauCeti.ClassFieldTheory.descendedInv_unique`: the two equations that characterize it.
* `TauCeti.ClassFieldTheory.descendedInv_res`, `TauCeti.ClassFieldTheory.descendedInv_conj`: its
  restriction and conjugation laws.
* `TauCeti.ClassFieldTheory.descendedInv_injective`,
  `TauCeti.ClassFieldTheory.range_descendedInv`: its injectivity and its image.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, §4.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F F' : Formation G}

/-! ### The descended invariant -/

variable (φ : F.toRep ⟶ F'.toRep) (σ : ∀ L : NormalLayer G, L.H F 2 →+ AddCircle (1 : ℚ))
  (hσ : ∀ {old new : NormalLayer G} (T : LayerRefinement old new) (y : old.H F 2),
    σ new (T.cohomologyInfl F 2 y) = σ old y)
  (hlift : ∀ (L : NormalLayer G) (x : L.H F' 2), ∃ (L' : NormalLayer G)
    (T : LayerRefinement L L') (y : L'.H F 2),
    groupCohomology.map (MonoidHom.id L'.Gal) (L'.repMap φ) 2 y = T.cohomologyInfl F' 2 x)
  (hker : ∀ (L : NormalLayer G) (y : L.H F 2),
    groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = 0 → σ L y = 0)
  (h1 : ∀ L : NormalLayer G, Subsingleton (L.H F' 1))
  (hσ₀ : ∀ (L : NormalLayer G) (y : L.H F 2), σ L y = 0 →
    groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = 0)
  (hres : ∀ {small big : NormalLayer G} (R : LayerRestriction small big) (y : big.H F 2),
    σ small (R.cohomologyRes F 2 y) = R.relativeDegree • σ big y)
  (hconj : ∀ (L : NormalLayer G) (g : G) (y : L.H F 2),
    σ (L.conjugate g) ((L.conjugateCohomologyIso F g 2).hom y) = σ L y)
  (hgen : ∀ L : NormalLayer G, ∃ (L' : NormalLayer G) (_ : LayerRefinement L L')
    (y : L'.H F 2), σ L' y = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)))

include hσ hker in
/-- Two lifts of inflations of one class, to two refinements, have the same value under `σ`: both
are inflated to a common refinement, where their difference is killed by `φ`. -/
private theorem eq_of_lift {L L₁ L₂ : NormalLayer G} (T₁ : LayerRefinement L L₁)
    (T₂ : LayerRefinement L L₂) {x : L.H F' 2} {y₁ : L₁.H F 2} {y₂ : L₂.H F 2}
    (h₁ : groupCohomology.map (MonoidHom.id L₁.Gal) (L₁.repMap φ) 2 y₁ =
      T₁.cohomologyInfl F' 2 x)
    (h₂ : groupCohomology.map (MonoidHom.id L₂.Gal) (L₂.repMap φ) 2 y₂ =
      T₂.cohomologyInfl F' 2 x) :
    σ L₁ y₁ = σ L₂ y₂ := by
  obtain ⟨M, S₁, S₂⟩ := LayerRefinement.exists_commonRefinement
    (T₁.same_ground.symm.trans T₂.same_ground)
  have hM : groupCohomology.map (MonoidHom.id M.Gal) (M.repMap φ) 2
      (S₁.cohomologyInfl F 2 y₁ - S₂.cohomologyInfl F 2 y₂) = 0 := by
    -- Both inflations are lifts of the inflation of `x` along the one refinement `L → M`.
    rw [map_sub, LayerRefinement.cohomologyInfl_comp_map_repMap_apply,
      LayerRefinement.cohomologyInfl_comp_map_repMap_apply, h₁, h₂,
      ← LayerRefinement.cohomologyInfl_trans_apply T₁ S₁,
      ← LayerRefinement.cohomologyInfl_trans_apply T₂ S₂, sub_self]
  rw [← hσ S₁, ← hσ S₂, ← sub_eq_zero, ← map_sub]
  exact hker M _ hM

/-- **The invariant of `F'` descended from `σ`**: the invariant of a class of `H²(L, A')` is the
value of `σ` on a lift, along `φ`, of its inflation to some refinement of `L`. By
`descendedInv_eq` it does not depend on the refinement or on the lift. -/
def descendedInv (L : NormalLayer G) : L.H F' 2 →+ AddCircle (1 : ℚ) :=
  AddMonoidHom.mk' (fun x ↦ σ (hlift L x).choose (hlift L x).choose_spec.choose_spec.choose)
    fun x₁ x₂ ↦ by
      obtain ⟨T₁, hT₁⟩ := (hlift L x₁).choose_spec
      obtain ⟨T₂, hT₂⟩ := (hlift L x₂).choose_spec
      obtain ⟨T, hT⟩ := (hlift L (x₁ + x₂)).choose_spec
      obtain ⟨M, S₁, S₂⟩ := LayerRefinement.exists_commonRefinement
        (T₁.same_ground.symm.trans T₂.same_ground)
      -- The sum of the two lifts, inflated to a common refinement, lifts `x₁ + x₂`.
      have h : groupCohomology.map (MonoidHom.id M.Gal) (M.repMap φ) 2
          (S₁.cohomologyInfl F 2 hT₁.choose + S₂.cohomologyInfl F 2 hT₂.choose) =
            (T₁.trans S₁).cohomologyInfl F' 2 (x₁ + x₂) := by
        rw [map_add, LayerRefinement.cohomologyInfl_comp_map_repMap_apply,
          LayerRefinement.cohomologyInfl_comp_map_repMap_apply, hT₁.choose_spec, hT₂.choose_spec,
          map_add, ← LayerRefinement.cohomologyInfl_trans_apply T₁ S₁,
          ← LayerRefinement.cohomologyInfl_trans_apply T₂ S₂]
      rw [eq_of_lift φ σ hσ hker T (T₁.trans S₁) hT.choose_spec h, map_add, hσ, hσ]

/-- **The invariant of a class is `σ` of any lift of any inflation of it**: if the inflation of
`x` to a refinement `L'` of `L` is the image under `φ` of `y`, then the descended invariant of `x`
is `σ_{L'} y`. -/
theorem descendedInv_eq {L L' : NormalLayer G} (T : LayerRefinement L L') {x : L.H F' 2}
    {y : L'.H F 2}
    (h : groupCohomology.map (MonoidHom.id L'.Gal) (L'.repMap φ) 2 y = T.cohomologyInfl F' 2 x) :
    descendedInv φ σ hσ hlift hker L x = σ L' y :=
  eq_of_lift φ σ hσ hker _ T (hlift L x).choose_spec.choose_spec.choose_spec h

/-- **On the image of `φ` the descended invariant is `σ`.** -/
@[simp]
theorem descendedInv_map {L : NormalLayer G} (y : L.H F 2) :
    descendedInv φ σ hσ hlift hker L
        (groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y) = σ L y :=
  descendedInv_eq φ σ hσ hlift hker (LayerRefinement.refl L) (by
    rw [LayerRefinement.cohomologyInfl_self, ConcreteCategory.id_apply])

/-- **The descended invariant does not change under inflation.** -/
@[simp]
theorem descendedInv_infl {old new : NormalLayer G} (T : LayerRefinement old new)
    (x : old.H F' 2) :
    descendedInv φ σ hσ hlift hker new (T.cohomologyInfl F' 2 x) =
      descendedInv φ σ hσ hlift hker old x := by
  obtain ⟨L', T', y, hy⟩ := hlift new (T.cohomologyInfl F' 2 x)
  rw [descendedInv_eq φ σ hσ hlift hker T' hy, descendedInv_eq φ σ hσ hlift hker (T.trans T')
    (hy.trans (LayerRefinement.cohomologyInfl_trans_apply T T' F' 2 x).symm)]

/-- **The descended invariant is determined by its two equations**: a family of homomorphisms
`H²(L, A') → ℚ/ℤ` that agrees with `σ` on the image of `φ` and does not change under inflation
is the descended invariant. -/
theorem descendedInv_unique (inv : ∀ L : NormalLayer G, L.H F' 2 →+ AddCircle (1 : ℚ))
    (hmap : ∀ (L : NormalLayer G) (y : L.H F 2),
      inv L (groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y) = σ L y)
    (hinfl : ∀ {old new : NormalLayer G} (T : LayerRefinement old new) (x : old.H F' 2),
      inv new (T.cohomologyInfl F' 2 x) = inv old x) :
    inv = descendedInv φ σ hσ hlift hker := by
  funext L
  ext x
  obtain ⟨L', T, y, hy⟩ := hlift L x
  rw [descendedInv_eq φ σ hσ hlift hker T hy, ← hinfl T, ← hy, hmap]

include hres in
/-- **Restriction multiplies the descended invariant by the relative degree**, as it does `σ`. -/
@[simp]
theorem descendedInv_res {small big : NormalLayer G} (R : LayerRestriction small big)
    (x : big.H F' 2) :
    descendedInv φ σ hσ hlift hker small (R.cohomologyRes F' 2 x) =
      R.relativeDegree • descendedInv φ σ hσ hlift hker big x := by
  obtain ⟨big', T, y, hy⟩ := hlift big x
  obtain ⟨small', T', R'⟩ := R.exists_refinement T
  -- The restriction of the lift `y` lifts the inflation of the restriction of `x`.
  have h : groupCohomology.map (MonoidHom.id small'.Gal) (small'.repMap φ) 2
      (R'.cohomologyRes F 2 y) = T'.cohomologyInfl F' 2 (R.cohomologyRes F' 2 x) := by
    rw [LayerRestriction.cohomologyRes_comp_map_repMap_apply, hy,
      LayerRestriction.cohomologyInfl_comp_cohomologyRes_apply R R' T T']
  have hdeg : R'.relativeDegree = R.relativeDegree := by
    rw [LayerRestriction.relativeDegree_def, LayerRestriction.relativeDegree_def,
      ← T'.same_ground_toSubgroup, ← T.same_ground_toSubgroup]
  rw [descendedInv_eq φ σ hσ hlift hker T' h, hres, descendedInv_eq φ σ hσ hlift hker T hy, hdeg]

include hconj in
/-- **Conjugation preserves the descended invariant**, as it does `σ`. -/
@[simp]
theorem descendedInv_conj (L : NormalLayer G) (g : G) (x : L.H F' 2) :
    descendedInv φ σ hσ hlift hker (L.conjugate g) ((L.conjugateCohomologyIso F' g 2).hom x) =
      descendedInv φ σ hσ hlift hker L x := by
  obtain ⟨L', T, y, hy⟩ := hlift L x
  -- The conjugate of the lift `y` lifts the inflation of the conjugate of `x`.
  have h : groupCohomology.map (MonoidHom.id (L'.conjugate g).Gal) ((L'.conjugate g).repMap φ) 2
      ((L'.conjugateCohomologyIso F g 2).hom y) =
        (T.conjugate g).cohomologyInfl F' 2 ((L.conjugateCohomologyIso F' g 2).hom x) := by
    rw [NormalLayer.conjugateCohomologyIso_hom_comp_map_repMap_apply, hy,
      LayerRefinement.cohomologyInfl_comp_conjugateCohomologyIso_hom_apply]
  rw [descendedInv_eq φ σ hσ hlift hker (T.conjugate g) h, hconj,
    descendedInv_eq φ σ hσ hlift hker T hy]

include h1 hσ₀ in
/-- **The descended invariant is injective** when `H¹` of every layer of `F'` vanishes and `σ`
vanishes only on the classes that `φ` kills: a class of invariant zero has a lift killed by `φ`,
so its inflation vanishes, and inflation is injective. -/
theorem descendedInv_injective (L : NormalLayer G) :
    Function.Injective (descendedInv φ σ hσ hlift hker L) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨L', T, y, hy⟩ := hlift L x
  rw [descendedInv_eq φ σ hσ hlift hker T hy] at hx
  refine T.cohomologyInfl_injective F' 1 (fun i hi ↦ ?_) ?_
  · obtain rfl : i = 0 := Nat.lt_one_iff.1 hi
    exact h1 _
  · rw [map_zero]
    exact hy.symm.trans (hσ₀ L' y hx)

include h1 hσ₀ hres hgen in
/-- **The image of the descended invariant of a layer of degree `n` is the `n`-torsion of `ℚ/ℤ`**
when, in addition to the hypotheses of `descendedInv_injective`, `σ` multiplies by the relative
degree under restriction and every layer, of degree `n`, has a refinement carrying a class with
`σ = 1/n`. -/
theorem range_descendedInv (L : NormalLayer G) :
    Set.range (descendedInv φ σ hσ hlift hker L) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) L.degree : Set (AddCircle (1 : ℚ))) := by
  refine Set.Subset.antisymm ?_ fun u hu ↦ ?_
  · -- The degree of `L` kills `H²(L, A')`.
    rintro _ ⟨x, rfl⟩
    refine AddSubgroup.torsionBy.nsmul_iff.2 ?_
    rw [← map_nsmul, L.degree_eq_natCard_gal, groupCohomology.natCard_nsmul_eq_zero, map_zero]
  obtain ⟨L', T, y, hy⟩ := hgen L
  set R := L'.subgroupRestriction T.galHom.ker
  -- Restricted to the layer `L'/L`, the class `y` has `σ = n • (1/n) = 0`, `n` the degree of `L`.
  have hRy : groupCohomology.map (MonoidHom.id (L'.subgroupLayer T.galHom.ker).Gal)
      ((L'.subgroupLayer T.galHom.ker).repMap φ) 2 (R.cohomologyRes F 2 y) = 0 := by
    refine hσ₀ _ _ ?_
    rw [hres, hy, L'.relativeDegree_subgroupRestriction, Subgroup.index_ker,
      MonoidHom.range_eq_top.2 T.galHom_surjective, Subgroup.card_top,
      ← NormalLayer.degree_eq_natCard_gal]
    exact AddSubgroup.torsionBy.nsmul_iff.1 (AddCircle.coe_period_div_mem_torsionBy (1 : ℚ))
  -- So the image of `y` restricts to zero on `L'/L` and is inflated from a class `x₀` of `L`.
  have hres' : R.cohomologyRes F' 2
      (groupCohomology.map (MonoidHom.id L'.Gal) (L'.repMap φ) 2 y) = 0 := by
    rwa [← LayerRestriction.cohomologyRes_comp_map_repMap_apply]
  obtain ⟨x₀, hx₀⟩ : groupCohomology.map (MonoidHom.id L'.Gal) (L'.repMap φ) 2 y ∈
      LinearMap.range (T.cohomologyInfl F' 2).hom :=
    (T.range_cohomologyInfl_eq_ker_cohomologyRes F' 1 fun i hi ↦ by
      obtain rfl : i = 0 := Nat.lt_one_iff.1 hi
      exact h1 _).ge hres'
  have hinv : descendedInv φ σ hσ hlift hker L x₀ = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)) :=
    (descendedInv_eq φ σ hσ hlift hker T hx₀.symm).trans hy
  obtain ⟨k, rfl⟩ := AddCircle.exists_zsmul_eq_of_mem_torsionBy (1 : ℚ)
    (Nat.cast_ne_zero.2 L.degree_pos.ne') hu
  exact ⟨k • x₀, by rw [map_zsmul, hinv]⟩

/-! ### The class formation of a descended invariant -/

/-- **The class formation of a descended invariant.** Let `σ` be an invariant of the layers of `F`
that does not change under inflation, multiplies by the relative degree under restriction and is
preserved by conjugation. Suppose that every class of `F'` lifts along `φ` after inflation to a
refinement, that `σ` vanishes exactly on the classes that `φ` kills, that every layer, of degree
`n`, has a refinement carrying a class with `σ = 1/n`, and that `H¹` of every layer of `F'`
vanishes. Then `F'` is a class formation, with the descended invariant as its invariant map. -/
def ClassFormation.ofDescendedInv : ClassFormation F' where
  subsingleton_h1 := h1
  inv := descendedInv φ σ hσ hlift hker
  inv_injective := descendedInv_injective φ σ hσ hlift hker h1 hσ₀
  range_inv := range_descendedInv φ σ hσ hlift hker h1 hσ₀ hres hgen
  inv_restrict := descendedInv_res φ σ hσ hlift hker hres
  inv_infl := descendedInv_infl φ σ hσ hlift hker
  inv_conj := descendedInv_conj φ σ hσ hlift hker hconj

/-- The invariant map of `ClassFormation.ofDescendedInv` is the descended invariant. -/
@[simp]
theorem ClassFormation.ofDescendedInv_inv :
    (ClassFormation.ofDescendedInv φ σ hσ hlift hker h1 hσ₀ hres hconj hgen).inv =
      descendedInv φ σ hσ hlift hker :=
  (rfl)

end TauCeti.ClassFieldTheory
