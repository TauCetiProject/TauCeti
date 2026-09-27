/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup

/-!
# Tate cohomology along an isomorphism of finite groups

Mathlib's Tate cohomology of a finite group is functorial in the coefficient representation, but
the group is fixed throughout. This file supplies the missing variance in the group for the case
of an isomorphism. A **compatible pair** consists of a group isomorphism `e : G ≃* H` and a
linear map `φ` between the coefficient modules of `M : Rep R G` and `N : Rep R H` satisfying

`φ ∘ ρ g = σ (e g) ∘ φ`,

which is Mathlib's `Representation.IsIntertwiningMap M.ρ (N.ρ.comp e) φ`; the general
representation-theoretic API of such a map lives in
`TauCeti.RepresentationTheory.Rep.ChangeOfGroup`.

Such a pair induces a map of Tate complexes, hence a map
`tateCohomology M n ⟶ tateCohomology N n` in every integer degree, and that map is an
isomorphism as soon as `φ` is.

The construction connects the two halves of the Tate complex: on the chain half it is Mathlib's
`groupHomology.chainsMap` along `e`, on the cochain half it is `groupCohomology.cochainsMap`
along `e.symm`, and the two agree on the Tate norm because `e` permutes the group, so the norm
`∑ g, ρ g` is carried to `∑ h, σ h`. In the degrees where Mathlib identifies Tate cohomology
with ordinary group cohomology or homology, the construction is the ordinary change-of-group map
of that theory.

The main application is conjugation: for an element of a group acting on a normal layer of a
class formation, conjugation is an isomorphism of finite Galois groups covered by an isomorphism
of coefficient modules, and the class-formation axioms compare the invariants of a layer with the
invariants of its conjugate through the resulting map in degree two.

## Main definitions

* `TauCeti.TateCohomology.complexMap`: the induced map of Tate complexes.
* `TauCeti.TateCohomology.map`: the induced map in a single integer degree.
* `TauCeti.TateCohomology.mapIso`: the induced isomorphism, for `φ` a linear equivalence.
* `TauCeti.TateCohomology.negSuccIso`: Mathlib's identification of Tate cohomology in degree
  `-(n+1)` with group homology in degree `n`, as an isomorphism of the two modules.
* `TauCeti.TateCohomology.resIso`: the packaged natural isomorphism
  `Res(e) ⋙ tateCohomologyFunctor n ≅ tateCohomologyFunctor n`.

## Main results

* `TauCeti.TateCohomology.complexMap_refl`: along the identity isomorphism the
  construction is Mathlib's coefficient functoriality.
* `TauCeti.TateCohomology.map_id` and `TauCeti.TateCohomology.map_comp`: functoriality in the
  compatible pair.
* `TauCeti.TateCohomology.map_comp_isoGroupCohomology_hom`: in positive degrees the construction
  is `groupCohomology.map` along `e.symm`.
* `TauCeti.TateCohomology.map_comp_isoGroupHomology_hom`: in degrees at most `-2` it is
  `groupHomology.map` along `e`; `TauCeti.TateCohomology.map_comp_negSuccIso_hom` restates this
  through `TauCeti.TateCohomology.negSuccIso`, which `TauCeti.TateCohomology.negSuccIso_hom`
  identifies with Mathlib's comparison.
* `TauCeti.TateCohomology.map_comp_H0IsoNormQuotient_hom`: in degree zero the construction is
  the map induced on the quotient of invariants by the norm image.
* `TauCeti.TateCohomology.HNegOneπ_comp_map`: in degree `-1` the construction sends the class of
  a norm-zero element to the class of its image (`TauCeti.TateCohomology.mapKerNorm`).
* `TauCeti.TateCohomology.H0π_comp_tateCohomologyFunctor_map`: in degree zero, Mathlib's
  coefficient functoriality sends the class of an invariant to the class of its image.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Chapter I, §5.
-/

public noncomputable section

universe u

open CategoryTheory Representation

namespace TauCeti.TateCohomology

variable {R G H K : Type u} [CommRing R] [Group G] [Group H] [Group K]
  {M : Rep R G} {N : Rep R H} {P : Rep R K}

section Complex

variable [Fintype G] [Fintype H] {e : G ≃* H} {φ : M.V →ₗ[R] N.V}

/-- The square joining the chain half of the Tate complex to its cochain half commutes for a
compatible pair: this is `IsIntertwiningMap.comp_norm` in degree zero. -/
theorem chainsMap_comp_d₀
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (groupHomology.chainsMap (e : G →* H) (IsIntertwiningMap.toRes hφ)).f 0 ≫
      (tateComplexConnectData N).d₀ =
      (tateComplexConnectData M).d₀ ≫
        (groupCohomology.cochainsMap (e.symm : H →* G) (IsIntertwiningMap.ofRes hφ)).f 0 := by
  simp only [tateComplexConnectData_d₀]
  ext x m y
  simp only [groupHomology.lsingle_comp_chainsMap_f_assoc, MonoidHom.coe_ofClass,
    ModuleCat.ofHom_comp, Category.assoc, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom,
    LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, Rep.tateNorm_eq,
    groupCohomology.cochainsMap_f, IsIntertwiningMap.toRes_hom_toLinearMap,
    IsIntertwiningMap.ofRes_hom_toLinearMap, Finsupp.lsum_single, LinearMap.pi_apply,
    LinearMap.compLeft_apply, LinearMap.funLeft_apply]
  exact congr($(IsIntertwiningMap.comp_norm hφ) m).symm

/-- **The map of Tate complexes attached to a compatible pair.** On the chain half it is
`groupHomology.chainsMap` along `e`, on the cochain half `groupCohomology.cochainsMap` along
`e.symm`. -/
def complexMap (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    tateComplex M ⟶ tateComplex N :=
  (tateComplexConnectData M).map (tateComplexConnectData N)
    (groupHomology.chainsMap (e : G →* H) (IsIntertwiningMap.toRes hφ))
    (groupCohomology.cochainsMap (e.symm : H →* G) (IsIntertwiningMap.ofRes hφ))
    (chainsMap_comp_d₀ hφ)

/-- In degree zero, the map of Tate complexes is the degree-zero component of
`groupCohomology.cochainsMap` along `e.symm`. -/
theorem complexMap_f_zero (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (complexMap hφ).f 0 =
      (groupCohomology.cochainsMap (e.symm : H →* G) (IsIntertwiningMap.ofRes hφ)).f 0 := by
  rw [complexMap, CochainComplex.ConnectData.map_f]

/-- In degree `-1`, the map of Tate complexes is the degree-zero component of
`groupHomology.chainsMap` along `e`. -/
theorem complexMap_f_negOne (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (complexMap hφ).f (-1) =
      (groupHomology.chainsMap (e : G →* H) (IsIntertwiningMap.toRes hφ)).f 0 := by
  rw [complexMap, CochainComplex.ConnectData.map_f]
  -- Mathlib states `map_f` only as a `match` on the degree; `-1` is `Int.negSucc 0` by
  -- definition, so the `match` selects the chain component (cf. `ConnectData.X_negOne`).
  rfl

/-- Under the identification `groupCohomology.cochainsIso₀` of the degree-zero term of the Tate
complex with the coefficient module, the degree-zero component of the map of Tate complexes becomes
`φ`. -/
@[reassoc]
theorem complexMap_f_zero_comp_cochainsIso₀_hom
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (complexMap hφ).f 0 ≫ (groupCohomology.cochainsIso₀ N).hom =
      (groupCohomology.cochainsIso₀ M).hom ≫ ModuleCat.ofHom φ := by
  rw [complexMap_f_zero]
  -- `exact` sees through `(tateComplex M).X 0 = (inhomogeneousCochains M).X 0` (`X_zero`).
  exact (groupCohomology.cochainsMap_f_0_comp_cochainsIso₀ _ _).trans <| by
    simp [Rep.Hom.toModuleCatHom]

/-- Under the identification `groupHomology.chainsIso₀` of the degree `-1` term of the Tate complex
with the coefficient module, the degree `-1` component of the map of Tate complexes becomes `φ`. -/
@[reassoc]
theorem complexMap_f_negOne_comp_chainsIso₀_hom
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (complexMap hφ).f (-1) ≫ (groupHomology.chainsIso₀ N).hom =
      (groupHomology.chainsIso₀ M).hom ≫ ModuleCat.ofHom φ := by
  rw [complexMap_f_negOne]
  -- `exact` sees through `(tateComplex M).X (-1) = (inhomogeneousChains M).X 0` (`X_negOne`).
  exact (groupHomology.chainsMap_f_0_comp_chainsIso₀ _ _).trans <| by
    simp [Rep.Hom.toModuleCatHom]

end Complex

section Degrees

variable [Fintype G] [Fintype H] [Fintype K]

/-- The map of Tate complexes depends only on the compatible pair, not on the compatibility
proof. -/
theorem complexMap_congr {e₁ e₂ : G ≃* H} {φ₁ φ₂ : M.V →ₗ[R] N.V}
    {h₁ : M.ρ.IsIntertwiningMap (N.ρ.comp (e₁ : G →* H)) φ₁}
    {h₂ : M.ρ.IsIntertwiningMap (N.ρ.comp (e₂ : G →* H)) φ₂}
    (he : e₁ = e₂) (hφ : φ₁ = φ₂) : complexMap h₁ = complexMap h₂ := by
  subst he; subst hφ; rfl

/-- **Along the identity isomorphism the construction is Mathlib's coefficient
functoriality.** -/
-- Deliberately not a `simp` lemma: its left-hand side subsumes that of the `@[simp]`
-- `complexMap_id`, and its right-hand side is a dead end for `simp`, which has no lemma carrying
-- `tateComplex.map (𝟙 M)` back to `𝟙 (tateComplex M)`.
theorem complexMap_refl {M N : Rep R G} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap
      (N.ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G)) φ) :
    complexMap hφ = tateComplex.map
      (Rep.ofHom ⟨φ, fun g ↦ by ext v; simpa using hφ.isIntertwining g v⟩ : M ⟶ N) := by
  rw [complexMap]
  congr 1
  · exact groupHomology.chainsMap_congr rfl (IsIntertwiningMap.toRes_hom_toLinearMap hφ)
  · exact groupCohomology.cochainsMap_congr rfl (IsIntertwiningMap.ofRes_hom_toLinearMap hφ)

/-- The identity compatible pair induces the identity of Tate complexes. -/
@[simp] theorem complexMap_id :
    complexMap (e := MulEquiv.refl G) (φ := LinearMap.id) (Rep.isIntertwiningMap_id M) =
      𝟙 (tateComplex M) := by
  rw [complexMap_refl]
  exact (tateComplexFunctor R G).map_id M

/-- **The construction is functorial in the compatible pair.** -/
-- The underlying monoid homomorphism of `e₁.trans e₂` is only extensionally equal to the
-- `MonoidHom.comp` in `IsIntertwiningMap.trans`, so the right-hand side transports across that
-- equality.
@[reassoc]
theorem complexMap_comp {e₁ : G ≃* H} {e₂ : H ≃* K} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e₁ : G →* H)) φ) {ψ : N.V →ₗ[R] P.V}
    (hψ : N.ρ.IsIntertwiningMap (P.ρ.comp (e₂ : H →* K)) ψ) :
    complexMap hφ ≫ complexMap hψ = complexMap (e := e₁.trans e₂) (φ := ψ ∘ₗ φ) (by
      convert IsIntertwiningMap.trans hφ hψ using 1
      ext x
      rfl) := by
  refine (CochainComplex.ConnectData.map_comp_map ..).trans ?_
  congr 1
  · refine (groupHomology.chainsMap_comp _ _ _ _).symm.trans
      (groupHomology.chainsMap_congr (by ext x; rfl) ?_)
    rw [IsIntertwiningMap.toRes_hom_toLinearMap]
    simp
  · refine (groupCohomology.cochainsMap_comp _ _ _ _).symm.trans
      (groupCohomology.cochainsMap_congr (by ext x; rfl) ?_)
    rw [IsIntertwiningMap.ofRes_hom_toLinearMap]
    simp

/-- **The isomorphism of Tate complexes attached to a compatible pair whose linear part is an
equivalence.** -/
def complexMapIso {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) :
    tateComplex M ≅ tateComplex N where
  hom := complexMap he
  inv := complexMap (IsIntertwiningMap.symm he)
  hom_inv_id := (complexMap_comp ..).trans
    ((complexMap_congr (by simp) (by ext x; simp)).trans
      complexMap_id)
  inv_hom_id := (complexMap_comp ..).trans
    ((complexMap_congr (by simp) (by ext x; simp)).trans
      complexMap_id)

@[simp] theorem complexMapIso_hom {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) :
    (complexMapIso he).hom = complexMap he := by
  rw [complexMapIso]

@[simp] theorem complexMapIso_inv {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) :
    (complexMapIso he).inv = complexMap (IsIntertwiningMap.symm he) := by
  rw [complexMapIso]

/-- **Tate cohomology along a compatible pair**, in a single integer degree. -/
def map {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) (n : ℤ) :
    tateCohomology M n ⟶ tateCohomology N n :=
  HomologicalComplex.homologyMap (complexMap hφ) n

/-- `TauCeti.TateCohomology.map` is the homology map of `complexMap`. This records the body of
`map`, whose definition is not exported. -/
theorem map_def {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) (n : ℤ) :
    map hφ n = HomologicalComplex.homologyMap (complexMap hφ) n := by rw [map]

/-- **Tate cohomology along a compatible pair whose linear part is an equivalence** is an
isomorphism in every integer degree. -/
def mapIso {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) (n : ℤ) :
    tateCohomology M n ≅ tateCohomology N n :=
  HomologicalComplex.homologyMapIso (complexMapIso he) n

@[simp] theorem mapIso_hom {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) (n : ℤ) :
    (mapIso he n).hom = map he n := by
  rw [mapIso, HomologicalComplex.homologyMapIso_hom, complexMapIso_hom, map_def]

@[simp] theorem mapIso_inv {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) (n : ℤ) :
    (mapIso he n).inv = map (IsIntertwiningMap.symm he) n := by
  rw [mapIso, HomologicalComplex.homologyMapIso_inv, complexMapIso_inv, map_def]

/-! ### Degree zero -/

/-- A compatible pair carries invariants to invariants. -/
def mapInvariants {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    M.ρ.invariants →ₗ[R] N.ρ.invariants :=
  (φ.comp M.ρ.invariants.subtype).codRestrict N.ρ.invariants fun x ↦ by
    rw [Representation.mem_invariants]
    intro h
    calc
      N.ρ h (φ x) = N.ρ (e (e.symm h)) (φ x) := by rw [e.apply_symm_apply]
      _ = φ (M.ρ (e.symm h) x) := (hφ.isIntertwining (e.symm h) x).symm
      _ = φ x := congrArg φ (x.2 (e.symm h))

omit [Fintype G] [Fintype H] in
@[simp]
theorem mapInvariants_apply_coe {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ)
    (x : M.ρ.invariants) : ((mapInvariants hφ x : N.ρ.invariants) : N.V) = φ x :=
  (rfl)

/-- The map on norm quotients induced by a compatible pair. -/
def mapNormQuotient {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    M.ρ.invariants ⧸ (LinearMap.range M.ρ.norm).submoduleOf M.ρ.invariants →ₗ[R]
      N.ρ.invariants ⧸ (LinearMap.range N.ρ.norm).submoduleOf N.ρ.invariants :=
  Submodule.mapQ _ _ (mapInvariants hφ) (by
    rintro ⟨_, hx⟩ ⟨y, rfl⟩
    refine ⟨φ y, ?_⟩
    rw [Submodule.subtype_apply, mapInvariants_apply_coe]
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun (Representation.IsIntertwiningMap.comp_norm hφ) y).symm)

/-- The map on norm quotients sends the class of an invariant to the class of its image. -/
@[simp]
theorem mapNormQuotient_mk {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) (x : M.ρ.invariants) :
    mapNormQuotient hφ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (mapInvariants hφ x) := by
  rw [mapNormQuotient, Submodule.mapQ_apply]

/-- Under the identifications `H0CyclesIso` of the degree-zero cycles of the Tate complexes of `M`
and `N` with the invariants, the map that `complexMap` induces on degree-zero cycles is
`mapInvariants`, the restriction of `φ` to the invariants. -/
@[reassoc]
theorem H0CyclesIso_inv_comp_cyclesMap {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (H0CyclesIso M).inv ≫ HomologicalComplex.cyclesMap (complexMap hφ) 0 =
      ModuleCat.ofHom (mapInvariants hφ) ≫ (H0CyclesIso N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  have := ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R N.V) N.ρ.invariants
  have hmap : ModuleCat.ofHom (mapInvariants hφ) ≫ ModuleCat.ofHom N.ρ.invariants.subtype =
      ModuleCat.ofHom M.ρ.invariants.subtype ≫ ModuleCat.ofHom φ :=
    ModuleCat.hom_ext <| LinearMap.ext <| mapInvariants_apply_coe hφ
  rw [← cancel_mono (ModuleCat.ofHom N.ρ.invariants.subtype), Category.assoc,
    H0CyclesIso_hom_comp_subtype, Category.assoc, hmap, H0CyclesIso_hom_comp_subtype_assoc]
  -- `H0CyclesIso_hom_comp_subtype` composes `(tateComplex N).iCycles 0` with `cochainsIso₀`, whose
  -- source is `(tateComplex N).X 0` only up to unfolding (`X_zero`); `rw` cannot match across it,
  -- so the remaining squares are composed, and reassociated, as terms.
  exact (HomologicalComplex.cyclesMap_i_assoc (complexMap hφ) 0 _).trans <|
    (congrArg ((tateComplex M).iCycles 0 ≫ ·) (complexMap_f_zero_comp_cochainsIso₀_hom hφ)).trans
      (Category.assoc _ _ _).symm

/-- The degree-zero Tate map sends the class of an invariant to the class of its image under the
compatible coefficient map. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_map {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    H0π M ≫ map hφ 0 = ModuleCat.ofHom (mapInvariants hφ) ≫ H0π N := by
  rw [H0π_eq_cyclesIso_inv_comp_homologyπ, H0π_eq_cyclesIso_inv_comp_homologyπ, map_def]
  -- `H0π` lands in `tateCohomology M 0`, which is `(tateComplex M).homology 0` only by unfolding
  -- the semireducible `tateCohomologyFunctor`. `rw` cannot match across that unfolding, not even
  -- `Category.assoc`, so the squares are composed, and reassociated, as terms.
  exact (Category.assoc _ _ _).trans <|
    (_ ≫= HomologicalComplex.homologyπ_naturality (complexMap hφ) 0).trans <|
      H0CyclesIso_inv_comp_cyclesMap_assoc hφ _

/-- In degree zero, the map attached to a compatible pair is the induced map on the quotient of
invariants by the norm image. -/
theorem map_comp_H0IsoNormQuotient_hom {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    map hφ 0 ≫ (H0IsoNormQuotient N).hom =
      (H0IsoNormQuotient M).hom ≫ ModuleCat.ofHom (mapNormQuotient hφ) := by
  rw [← cancel_epi (H0π M)]
  rw [← Category.assoc, H0π_comp_map, Category.assoc,
    H0π_comp_H0IsoNormQuotient_hom]
  rw [H0π_comp_H0IsoNormQuotient_hom_assoc]
  ext x
  simp [mapNormQuotient]

/-! ### Degree minus one -/

/-- A compatible pair carries norm-zero elements to norm-zero elements. -/
def mapKerNorm {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    LinearMap.ker M.ρ.norm →ₗ[R] LinearMap.ker N.ρ.norm :=
  (φ.comp (LinearMap.ker M.ρ.norm).subtype).codRestrict (LinearMap.ker N.ρ.norm) fun x ↦ by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← LinearMap.comp_apply,
      ← Representation.IsIntertwiningMap.comp_norm hφ, LinearMap.comp_apply,
      LinearMap.mem_ker.1 x.2, map_zero]

@[simp]
theorem mapKerNorm_apply_coe {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ)
    (x : LinearMap.ker M.ρ.norm) :
    ((mapKerNorm hφ x : LinearMap.ker N.ρ.norm) : N.V) = φ x :=
  (rfl)

/-- Under the identifications `HNegOneCyclesIso` of the degree `-1` cycles of the Tate complexes of
`M` and `N` with the kernels of the norms, the map that `complexMap` induces on degree `-1` cycles
is `mapKerNorm`, the restriction of `φ` to the elements of norm zero. -/
@[reassoc]
theorem HNegOneCyclesIso_inv_comp_cyclesMap {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    (HNegOneCyclesIso M).inv ≫ HomologicalComplex.cyclesMap (complexMap hφ) (-1) =
      ModuleCat.ofHom (mapKerNorm hφ) ≫ (HNegOneCyclesIso N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  have := ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R N.V) (LinearMap.ker N.ρ.norm)
  have hmap : ModuleCat.ofHom (mapKerNorm hφ) ≫ ModuleCat.ofHom (LinearMap.ker N.ρ.norm).subtype =
      ModuleCat.ofHom (LinearMap.ker M.ρ.norm).subtype ≫ ModuleCat.ofHom φ :=
    ModuleCat.hom_ext <| LinearMap.ext <| mapKerNorm_apply_coe hφ
  rw [← cancel_mono (ModuleCat.ofHom (LinearMap.ker N.ρ.norm).subtype), Category.assoc,
    HNegOneCyclesIso_hom_comp_subtype, Category.assoc, hmap,
    HNegOneCyclesIso_hom_comp_subtype_assoc]
  -- `HNegOneCyclesIso_hom_comp_subtype` composes `(tateComplex N).iCycles (-1)` with `chainsIso₀`,
  -- whose source is `(tateComplex N).X (-1)` only up to unfolding (`X_negOne`); `rw` cannot match
  -- across it, so the remaining squares are composed, and reassociated, as terms.
  exact (HomologicalComplex.cyclesMap_i_assoc (complexMap hφ) (-1) _).trans <|
    (congrArg ((tateComplex M).iCycles (-1) ≫ ·)
      (complexMap_f_negOne_comp_chainsIso₀_hom hφ)).trans (Category.assoc _ _ _).symm

/-- The degree `-1` Tate map sends the class of a norm-zero element to the class of its image
under the compatible coefficient map. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem HNegOneπ_comp_map {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) :
    HNegOneπ M ≫ map hφ (-1) = ModuleCat.ofHom (mapKerNorm hφ) ≫ HNegOneπ N := by
  rw [HNegOneπ_eq_cyclesIso_inv_comp_homologyπ, HNegOneπ_eq_cyclesIso_inv_comp_homologyπ,
    map_def]
  -- `HNegOneπ` lands in `tateCohomology M (-1)`, which is `(tateComplex M).homology (-1)` only by
  -- unfolding the semireducible `tateCohomologyFunctor`. `rw` cannot match across that unfolding,
  -- not even `Category.assoc`, so the squares are composed, and reassociated, as terms.
  exact (Category.assoc _ _ _).trans <|
    (_ ≫= HomologicalComplex.homologyπ_naturality (complexMap hφ) (-1)).trans <|
      HNegOneCyclesIso_inv_comp_cyclesMap_assoc hφ _

/-- Tate cohomology in a fixed degree depends only on the compatible pair. -/
theorem map_congr {e₁ e₂ : G ≃* H} {φ₁ φ₂ : M.V →ₗ[R] N.V}
    {h₁ : M.ρ.IsIntertwiningMap (N.ρ.comp (e₁ : G →* H)) φ₁}
    {h₂ : M.ρ.IsIntertwiningMap (N.ρ.comp (e₂ : G →* H)) φ₂}
    (he : e₁ = e₂) (hφ : φ₁ = φ₂) (n : ℤ) :
    map h₁ n = map h₂ n := by
  rw [map_def, map_def, complexMap_congr he hφ]

/-- Along the identity isomorphism, Tate cohomology of a compatible pair is Mathlib's coefficient
functoriality. -/
-- As for `complexMap_refl`, deliberately not a `simp` lemma: it would subsume the
-- `@[simp]` `map_id` and leave `simp` stuck on the identity, since `Rep.ofHom ⟨LinearMap.id, _⟩`
-- has no `simp` route to `𝟙 M`.
theorem map_refl {M N : Rep R G} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap
      (N.ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G)) φ) (n : ℤ) :
    map hφ n = (tateCohomologyFunctor n).map
      (Rep.ofHom ⟨φ, fun g ↦ by ext v; simpa using hφ.isIntertwining g v⟩ : M ⟶ N) := by
  rw [map_def, complexMap_refl]
  exact (HomologicalComplex.homologyFunctor_map (ModuleCat R) (ComplexShape.up ℤ) n _).symm

/-- The identity compatible pair induces the identity in every degree. -/
@[simp] theorem map_id (n : ℤ) :
    map (e := MulEquiv.refl G) (φ := LinearMap.id) (Rep.isIntertwiningMap_id M) n =
      𝟙 (tateCohomology M n) := by
  rw [map_def, complexMap_id]
  exact HomologicalComplex.homologyMap_id _ _

/-- **Tate cohomology is functorial in the compatible pair**, in every degree. -/
-- As in `complexMap_comp`, the right-hand side transports the generalized composition theorem
-- across the extensional equality of the two underlying monoid homomorphisms.
@[reassoc]
theorem map_comp {e₁ : G ≃* H} {e₂ : H ≃* K} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e₁ : G →* H)) φ) {ψ : N.V →ₗ[R] P.V}
    (hψ : N.ρ.IsIntertwiningMap (P.ρ.comp (e₂ : H →* K)) ψ) (n : ℤ) :
    map hφ n ≫ map hψ n = map (e := e₁.trans e₂) (φ := ψ ∘ₗ φ) (by
      convert IsIntertwiningMap.trans hφ hψ using 1
      ext x
      rfl) n := by
  rw [map_def, map_def, map_def, ← complexMap_comp hφ hψ,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- **In positive degrees the construction is the ordinary cohomological change-of-group map**
along `e.symm`, read through Mathlib's comparison between Tate and group cohomology. -/
theorem map_comp_isoGroupCohomology_hom {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) (n : ℕ) [NeZero n] :
    map hφ (n : ℤ) ≫ (_root_.TateCohomology.isoGroupCohomology n).hom.app N =
      (_root_.TateCohomology.isoGroupCohomology n).hom.app M ≫
        groupCohomology.map (e.symm : H →* G) (IsIntertwiningMap.ofRes hφ) n := by
  have key : HomologicalComplex.homologyMap (complexMap hφ) (n : ℤ) ≫
      ((tateComplexConnectData N).homologyIsoPos n (n : ℤ) rfl).hom =
        ((tateComplexConnectData M).homologyIsoPos n (n : ℤ) rfl).hom ≫
          HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap (e.symm : H →* G) (IsIntertwiningMap.ofRes hφ)) n := by
    rw [complexMap, CochainComplex.ConnectData.homologyMap_map_of_eq_succ
      (n := n) (m := (n : ℤ)) (hmn := rfl)]
    simp
  rw [map_def]
  -- What is left is Mathlib's own unfoldings, all of which cross `tateCohomologyFunctor`, a
  -- semireducible `def`: `isoGroupCohomology` is `homologyIsoPos` componentwise,
  -- `groupCohomology.map` is `homologyMap` of `cochainsMap`, and `tateCohomology M n` is the
  -- homology of `tateComplex M`.
  -- `rw`/`simp` cannot cross them, because their motives are ill-typed at `implicit` transparency.
  exact key

/-- **In degrees at most `-2` the construction is the ordinary homological change-of-group map**
along `e`, read through Mathlib's comparison between Tate cohomology and group homology. -/
theorem map_comp_isoGroupHomology_hom {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ)
    (m : ℤ) (n : ℕ) (hmn : m = -(n + 1)) [NeZero n] :
    map hφ m ≫ (_root_.TateCohomology.isoGroupHomology m n hmn).hom.app N =
      (_root_.TateCohomology.isoGroupHomology m n hmn).hom.app M ≫
        groupHomology.map (e : G →* H) (IsIntertwiningMap.toRes hφ) n := by
  have key : HomologicalComplex.homologyMap (complexMap hφ) m ≫
      ((tateComplexConnectData N).homologyIsoNeg n m hmn).hom =
        ((tateComplexConnectData M).homologyIsoNeg n m hmn).hom ≫
          HomologicalComplex.homologyMap
            (groupHomology.chainsMap (e : G →* H) (IsIntertwiningMap.toRes hφ)) n := by
    rw [complexMap, CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ
      (n := n) (m := m) (hmn := hmn)]
    simp
  rw [map_def]
  -- As above: `isoGroupHomology` is `homologyIsoNeg` componentwise, `groupHomology.map` is
  -- `homologyMap` of `chainsMap`, and `tateCohomology M m` is the homology of `tateComplex M`.
  exact key

variable (M) in
/-- Tate cohomology in degree `-(n+1)`, for `n > 0`, is group homology in degree `n`: the
component at `M` of Mathlib's comparison `TateCohomology.isoGroupHomology`. -/
def negSuccIso (n : ℕ) [NeZero n] :
    tateCohomology M (Int.negSucc n) ≅ groupHomology M n :=
  (_root_.TateCohomology.isoGroupHomology (Int.negSucc n) n (Int.negSucc_eq n)).app M

variable (M) in
/-- `TauCeti.TateCohomology.negSuccIso` is the component at `M` of Mathlib's comparison
`TateCohomology.isoGroupHomology`. -/
theorem negSuccIso_hom (n : ℕ) [NeZero n] :
    (negSuccIso M n).hom =
      ((_root_.TateCohomology.isoGroupHomology (Int.negSucc n) n (Int.negSucc_eq n)).app M).hom :=
  (rfl)

/-- **In degrees `-(n+1)` with `n > 0` the construction is the ordinary homological
change-of-group map** along `e`, read through `TauCeti.TateCohomology.negSuccIso`. -/
@[reassoc (attr := simp)]
theorem map_comp_negSuccIso_hom {e : G ≃* H} {φ : M.V →ₗ[R] N.V}
    (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) φ) (n : ℕ) [NeZero n] :
    map hφ (Int.negSucc n) ≫ (negSuccIso N n).hom =
      (negSuccIso M n).hom ≫ groupHomology.map (e : G →* H) (IsIntertwiningMap.toRes hφ) n :=
  map_comp_isoGroupHomology_hom hφ _ n (Int.negSucc_eq n)

/-- **Restricting the coefficients along an isomorphism of finite groups does not change Tate
cohomology**, naturally in the coefficients. -/
def resIso (e : G ≃* H) (n : ℤ) :
    Rep.resFunctor (e : G →* H) ⋙ tateCohomologyFunctor (R := R) (G := G) n ≅
      tateCohomologyFunctor n :=
  NatIso.ofComponents (fun N ↦ mapIso (Rep.isIntertwiningMap_res N (e : G →* H)) n)
    fun {N N'} ψ ↦ by
      have hψ : N.ρ.IsIntertwiningMap
          (N'.ρ.comp ((MulEquiv.refl H : H ≃* H) : H →* H)) ψ.hom.toLinearMap :=
        ⟨fun g v ↦ congr($(ψ.hom.isIntertwining' g) v)⟩
      have hres : (Rep.res (e : G →* H) N).ρ.IsIntertwiningMap
          ((Rep.res (e : G →* H) N').ρ.comp
            ((MulEquiv.refl G : G ≃* G) : G →* G))
          (ψ.hom.toLinearMap :
            (Rep.res (e : G →* H) N).V →ₗ[R] (Rep.res (e : G →* H) N').V) :=
        ⟨fun g v ↦ congr($(ψ.hom.isIntertwining' (e g)) v)⟩
      have key : map (e := MulEquiv.refl G) hres n ≫
          map (Rep.isIntertwiningMap_res N' (e : G →* H)) n =
          map (Rep.isIntertwiningMap_res N (e : G →* H)) n ≫
            map (e := MulEquiv.refl H) hψ n := by
        rw [map_comp, map_comp]
        exact map_congr (by ext x; rfl) (by ext x; rfl) n
      have hsrc : (Rep.resFunctor (e : G →* H) ⋙ tateCohomologyFunctor (R := R) (G := G) n).map ψ =
          map (e := MulEquiv.refl G) hres n := (map_refl hres n).symm
      have htgt : (tateCohomologyFunctor n).map ψ = map (e := MulEquiv.refl H) hψ n :=
        (map_refl hψ n).symm
      rw [hsrc, htgt, mapIso_hom, mapIso_hom]
      exact key

@[simp] theorem resIso_hom_app (e : G ≃* H) (n : ℤ) (N : Rep R H) :
    (resIso e n).hom.app N = (mapIso (Rep.isIntertwiningMap_res N (e : G →* H)) n).hom := by
  rw [resIso]
  -- `NatIso.ofComponents_hom_app` is not usable as a rewrite here: its motive is ill-typed at
  -- `implicit` transparency, because `tateCohomologyFunctor` is a semireducible `def`.
  rfl

@[simp] theorem resIso_inv_app (e : G ≃* H) (n : ℤ) (N : Rep R H) :
    (resIso e n).inv.app N = (mapIso (Rep.isIntertwiningMap_res N (e : G →* H)) n).inv := by
  rw [resIso]
  -- As above for `NatIso.ofComponents_inv_app`.
  rfl

/-- Tate cohomology groups matched by a compatible pair whose linear part is an equivalence have
the same cardinality. -/
theorem natCard_tateCohomology_eq {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) (n : ℤ) :
    Nat.card (tateCohomology M n) = Nat.card (tateCohomology N n) :=
  Nat.card_congr (mapIso he n).toLinearEquiv.toEquiv

/-- In degree zero, the map induced by a morphism of representations of one finite group sends
the class of an invariant to the class of its image. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_tateCohomologyFunctor_map {M N : Rep R G} (f : M ⟶ N) :
    H0π M ≫ (tateCohomologyFunctor 0).map f = (Rep.invariantsFunctor R G).map f ≫ H0π N := by
  have hf : M.ρ.IsIntertwiningMap (N.ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G))
      f.hom.toLinearMap := ⟨fun g v ↦ Rep.hom_comm_apply f g v⟩
  -- `map_refl` produces `Rep.ofHom ⟨f.hom.toLinearMap, _⟩`, which is `f` by structure eta.
  have h : map hf 0 = (tateCohomologyFunctor 0).map f := map_refl hf 0
  rw [← h, H0π_comp_map]
  -- `mapInvariants hf` restricts `f` to the invariants, which is how `Rep.invariantsFunctor` acts.
  rfl

end Degrees

end TateCohomology

end TauCeti
