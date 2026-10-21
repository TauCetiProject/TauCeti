/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.NumberTheory.Padics.QuotientTower

/-!
# Measures in the coordinates of a tower of finite quotients

Let `Γ` be a compact group presented by a tower of finite quotients `q n : Γ → A n`
(`TauCeti.FiniteQuotientTower`). The finite projections `π_{q n}(μ) : A n →₀ R` of a measure
`μ ∈ D(Γ, R)`, which record the measures of the fibres of `q n`, form a family that is compatible
under the transition maps: pushing the coordinates at level `n` forward to a level `m ≤ n` gives
the coordinates at level `m`. This file shows that, for integral coefficients, these coordinates
identify measures with compatible families: every compatible family `c n : A n →₀ ℤ_p` is the
family of coordinates of exactly one measure `μ ∈ D(Γ, ℤ_p)`.

Uniqueness holds over every Hausdorff topological coefficient ring, because the levels of a tower
are cofinal among the finite quotients `Γ ⧸ U` by open normal subgroups. Existence is read off the
identification of integral measures with the completed group algebra
(`AbstractMeasure.completedGroupAlgebraEquiv`): a compatible family along the tower pushes forward
to a compatible family over all open normal subgroups.

For the congruence tower of `ℤ_pˣ`, whose levels are the reductions `ℤ_pˣ → (ℤ/p^nℤ)ˣ`, this
describes the integral measures on `ℤ_pˣ` by their unit coordinates.

## Main definitions

* `AbstractMeasure.towerCoordinates`: the linear map sending a measure to its family of finite
  projections along a tower.
* `AbstractMeasure.towerCoordinatesEquiv`: for integral coefficients, the linear equivalence
  between measures and compatible families.

## Main results

* `AbstractMeasure.towerCoordinates_injective`: a measure is determined by its finite projections
  along a tower.
* `AbstractMeasure.existsUnique_finiteProjection_eq`: every compatible integral family is the
  family of finite projections of a unique integral measure.
* `AbstractMeasure.existsUnique_finiteProjection_unitsToZModPow_eq`: the same statement for the
  congruence tower of `ℤ_pˣ`, describing integral measures on `ℤ_pˣ` by their unit coordinates.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Ann. Math. Qué.
  (2024), Remarks 3.11–3.12 and Proposition 3.16 with its proof.
-/

public noncomputable section

open ContinuousMap TauCeti

namespace AbstractMeasure

-- The levels of a tower of a compact group are finite (`FiniteQuotientTower.finite`); finiteness is
-- assumed as an instance because the finite projections along the levels require it.
variable {Γ R : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {A : ℕ → Type*} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)] [∀ n, DiscreteTopology (A n)]
  [∀ n, Finite (A n)] (T : FiniteQuotientTower Γ A)

section TopologicalRing

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- The finite projections of a measure along the levels of a tower are compatible: pushing the
projection at level `n` forward along the transition map to `m ≤ n` gives the projection at
level `m`. -/
theorem mapDomain_finiteProjection_q {m n : ℕ} (h : m ≤ n) (μ : D(Γ, R)) :
    (finiteProjection (T.q n : C(Γ, A n)) μ).mapDomain (T.t h) =
      finiteProjection (T.q m : C(Γ, A m)) μ := by
  have hq : (T.q m : C(Γ, A m)) =
      (⟨T.t h, continuous_of_discreteTopology⟩ : C(A n, A m)).comp (T.q n) := by
    ext
    simp
  rw [hq, finiteProjection_comp, ContinuousMap.coe_mk]

/-- **Tower coordinates of a measure.** The linear map sending a measure on `Γ` to the
compatible family of its finite projections along the levels of a tower. -/
def towerCoordinates : D(Γ, R) →ₗ[R] T.compatibleFamilies R where
  toFun μ := ⟨fun n ↦ finiteProjection (T.q n : C(Γ, A n)) μ,
    FiniteQuotientTower.mem_compatibleFamilies.mpr fun _ _ h ↦ mapDomain_finiteProjection_q T h μ⟩
  map_add' μ ν := by ext; simp
  map_smul' r μ := by ext; simp

/-- The coordinate of `towerCoordinates T μ` at level `n` is the finite projection of `μ` along the
`n`-th level. -/
@[simp]
theorem towerCoordinates_apply (μ : D(Γ, R)) (n : ℕ) :
    (towerCoordinates T μ : ∀ n, A n →₀ R) n = finiteProjection (T.q n : C(Γ, A n)) μ :=
  (rfl)

/-- The projection of a measure to a quotient `Γ ⧸ U` coarser than a level of the tower is the
pushforward of its coordinates at that level. -/
private theorem finiteProjection_quotientMk {n : ℕ} {U : OpenNormalSubgroup Γ}
    (h : (T.ker n : Subgroup Γ) ≤ U) (μ : D(Γ, R)) :
    finiteProjection (U.toSubgroup.quotientMkContinuousMonoidHom : C(Γ, Γ ⧸ U.toSubgroup)) μ =
      (finiteProjection (T.q n : C(Γ, A n)) μ).mapDomain (T.toQuotient h) := by
  have hq : (U.toSubgroup.quotientMkContinuousMonoidHom : C(Γ, Γ ⧸ U.toSubgroup)) =
      (⟨T.toQuotient h, continuous_of_discreteTopology⟩ : C(A n, Γ ⧸ U.toSubgroup)).comp
        (T.q n) := by
    ext
    simp
  rw [hq, finiteProjection_comp, ContinuousMap.coe_mk]

/-- **Tower coordinates determine a measure.** Over a Hausdorff coefficient ring, two measures on
`Γ` with the same finite projections at every level of a tower are equal. -/
theorem towerCoordinates_injective [T2Space R] :
    Function.Injective (towerCoordinates (R := R) T) := by
  intro μ ν hμν
  have := T.totallyDisconnectedSpace
  refine toCompletedGroupAlgebra_injective (completedGroupAlgebra.ext fun U ↦ ?_)
  obtain ⟨n, hn⟩ := T.exists_ker_le_of_isOpen U.isOpen
  apply MonoidAlgebra.coeff_injective
  have hn' := congrArg (fun c : T.compatibleFamilies R ↦ (c : ∀ n, A n →₀ R) n) hμν
  simp only [towerCoordinates_apply] at hn'
  simp only [proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_apply,
    MonoidAlgebra.coeff_ofCoeff, finiteProjection_quotientMk T hn, hn']

end TopologicalRing

section PadicInt

variable {p : ℕ} [Fact p.Prime]

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [∀ n, Finite (A n)] in
/-- The pushforward of a compatible family to `Γ ⧸ U` does not depend on the level of the tower
through which `Γ → Γ ⧸ U` is factored. -/
private theorem mapDomain_toQuotient_eq {c : ∀ n, A n →₀ ℤ_[p]}
    (hc : c ∈ T.compatibleFamilies ℤ_[p]) {U : OpenNormalSubgroup Γ} {m n : ℕ}
    (hm : (T.ker m : Subgroup Γ) ≤ U) (hn : (T.ker n : Subgroup Γ) ≤ U) :
    (c m).mapDomain (T.toQuotient hm) = (c n).mapDomain (T.toQuotient hn) := by
  -- Both sides are the pushforward of the coefficients at the common deeper level `max m n`.
  have key {k l : ℕ} (hkl : k ≤ l) (hk : (T.ker k : Subgroup Γ) ≤ U) :
      (c k).mapDomain (T.toQuotient hk) =
        (c l).mapDomain (T.toQuotient (le_trans (α := Subgroup Γ) (T.ker_antitone hkl) hk)) := by
    rw [← FiniteQuotientTower.mem_compatibleFamilies.mp hc hkl, ← Finsupp.mapDomain_comp]
    congr 1
    ext a
    simp
  rw [key (le_max_left m n) hm, key (le_max_right m n) hn]

/-- The family of elements of the group algebras `ℤ_p[Γ ⧸ U]` obtained by pushing a compatible
family forward from a level of the tower contained in `U`. -/
private def quotientFamily (c : ∀ n, A n →₀ ℤ_[p]) (U : OpenNormalSubgroup Γ) :
    MonoidAlgebra ℤ_[p] (Γ ⧸ U.toSubgroup) :=
  MonoidAlgebra.ofCoeff ((c (T.exists_ker_le_of_isOpen U.isOpen).choose).mapDomain
    (T.toQuotient (T.exists_ker_le_of_isOpen U.isOpen).choose_spec))

omit [∀ n, Finite (A n)] in
private theorem coeff_quotientFamily {c : ∀ n, A n →₀ ℤ_[p]}
    (hc : c ∈ T.compatibleFamilies ℤ_[p]) {U : OpenNormalSubgroup Γ} {n : ℕ}
    (hn : (T.ker n : Subgroup Γ) ≤ U) :
    (quotientFamily T c U).coeff = (c n).mapDomain (T.toQuotient hn) :=
  mapDomain_toQuotient_eq T hc _ hn

/-- **Tower coordinates are onto the compatible families.** Every compatible integral family
along a tower is the family of finite projections of an integral measure. -/
theorem towerCoordinates_surjective :
    Function.Surjective (towerCoordinates (R := ℤ_[p]) T) := by
  have := T.totallyDisconnectedSpace
  rintro ⟨c, hc⟩
  -- Assemble the pushforwards of `c` to all finite quotients into an element of `ℤ_p[[Γ]]`.
  have hx ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V) :
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (quotientFamily T c U) =
        quotientFamily T c V := by
    obtain ⟨n, hn⟩ := T.exists_ker_le_of_isOpen U.isOpen
    have hnV : (T.ker n : Subgroup Γ) ≤ V := hn.trans hUV
    apply MonoidAlgebra.coeff_injective
    rw [MonoidAlgebra.coeff_mapDomain, coeff_quotientFamily T hc hn,
      coeff_quotientFamily T hc hnV, ← Finsupp.mapDomain_comp]
    congr 1
    ext a
    obtain ⟨x, rfl⟩ := T.surjective_q n a
    simp
  obtain ⟨μ, hμ⟩ := toCompletedGroupAlgebra_surjective (completedGroupAlgebra.mk ℤ_[p] Γ _ hx)
  refine ⟨μ, Subtype.ext (funext fun n ↦ Finsupp.mapDomain_injective (T.toQuotient_injective n)
    ?_)⟩
  -- At the kernel of level `n`, both families push forward to the projection of `μ`.
  have hproj := congrArg (fun y ↦ (completedGroupAlgebra.proj ℤ_[p] Γ (T.ker n) y).coeff) hμ
  simp only [proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_apply,
    MonoidAlgebra.coeff_ofCoeff, finiteProjection_quotientMk T le_rfl,
    completedGroupAlgebra.proj_mk, coeff_quotientFamily T hc le_rfl] at hproj
  exact hproj

/-- **Integral measures are the compatible families along a tower.** For a compact group with a
tower of finite quotients, sending an integral measure to its finite projections at all levels is
a linear equivalence onto the compatible families. -/
def towerCoordinatesEquiv : D(Γ, ℤ_[p]) ≃ₗ[ℤ_[p]] T.compatibleFamilies ℤ_[p] :=
  LinearEquiv.ofBijective (towerCoordinates T)
    ⟨towerCoordinates_injective T, towerCoordinates_surjective T⟩

/-- The forward map of `towerCoordinatesEquiv` is `towerCoordinates`. -/
@[simp]
theorem towerCoordinatesEquiv_apply (μ : D(Γ, ℤ_[p])) :
    towerCoordinatesEquiv T μ = towerCoordinates T μ :=
  (rfl)

/-- The measure with prescribed tower coordinates has those coordinates as its finite
projections. -/
@[simp]
theorem finiteProjection_towerCoordinatesEquiv_symm (c : T.compatibleFamilies ℤ_[p]) (n : ℕ) :
    finiteProjection (T.q n : C(Γ, A n)) ((towerCoordinatesEquiv T).symm c) =
      (c : ∀ n, A n →₀ ℤ_[p]) n := by
  rw [← towerCoordinates_apply, ← towerCoordinatesEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The total mass of the measure with prescribed tower coordinates is the sum of its
coefficients at any level. -/
theorem towerCoordinatesEquiv_symm_apply_one (c : T.compatibleFamilies ℤ_[p]) (n : ℕ) :
    (towerCoordinatesEquiv T).symm c 1 = ((c : ∀ n, A n →₀ ℤ_[p]) n).sum fun _ r ↦ r := by
  rw [← finiteProjection_towerCoordinatesEquiv_symm, sum_finiteProjection]

/-- **Existence and uniqueness from tower coordinates.** Every compatible integral family along a
tower of finite quotients of `Γ` is the family of finite projections of a unique integral measure
on `Γ`. -/
theorem existsUnique_finiteProjection_eq {c : ∀ n, A n →₀ ℤ_[p]}
    (hc : c ∈ T.compatibleFamilies ℤ_[p]) :
    ∃! μ : D(Γ, ℤ_[p]), ∀ n, finiteProjection (T.q n : C(Γ, A n)) μ = c n := by
  refine ⟨(towerCoordinatesEquiv T).symm ⟨c, hc⟩,
    fun n ↦ finiteProjection_towerCoordinatesEquiv_symm T ⟨c, hc⟩ n, fun μ hμ ↦ ?_⟩
  rw [LinearEquiv.eq_symm_apply]
  ext n : 2
  exact hμ n

/-- **Integral measures on `ℤ_pˣ` from unit coordinates.** For every family of coefficients
`c n : (ℤ/p^nℤ)ˣ →₀ ℤ_p` compatible under the reductions `(ℤ/p^nℤ)ˣ → (ℤ/p^mℤ)ˣ`, there is a
unique integral measure on `ℤ_pˣ` whose finite projection along the reduction
`ℤ_pˣ → (ℤ/p^nℤ)ˣ` is `c n` for every `n`. -/
theorem existsUnique_finiteProjection_unitsToZModPow_eq {c : ∀ n, (ZMod (p ^ n))ˣ →₀ ℤ_[p]}
    (hc : ∀ ⦃m n : ℕ⦄ (h : m ≤ n), (c n).mapDomain (ZMod.unitsMap (pow_dvd_pow p h)) = c m) :
    ∃! μ : D(ℤ_[p]ˣ, ℤ_[p]),
      ∀ n, finiteProjection (PadicInt.unitsToZModPow (p := p) n : C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) μ =
        c n := by
  simpa using existsUnique_finiteProjection_eq (FiniteQuotientTower.unitTower p) (c := c)
    (by simpa using hc)

end PadicInt

/-! The measure whose coordinates are the point masses `single (q n x) a` is `a • δ_x`. -/

example {p : ℕ} [Fact p.Prime] (x : Γ) (a : ℤ_[p]) :
    (towerCoordinatesEquiv T).symm ⟨fun n ↦ Finsupp.single (T.q n x) a,
      FiniteQuotientTower.mem_compatibleFamilies.mpr fun m n h ↦ by simp⟩ =
      a • dirac ℤ_[p] x := by
  rw [LinearEquiv.symm_apply_eq]
  ext n : 2
  simp

end AbstractMeasure
