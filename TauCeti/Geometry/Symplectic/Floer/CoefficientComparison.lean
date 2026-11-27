/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PeriodGroup
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.Grading

/-!
# Comparing quantum and Floer coefficients

Quantum coefficients use the area period `ω`, whereas Floer coefficients use the negative
area period. The comparison sends a class `A` to the negative of its image in the chosen
Floer class group: `q^A ↦ e^(-q A)`. This preserves periods, so it extends to a continuous
unital homomorphism of the completed rings. Its coefficients are finite sums even if the
class-group map has infinite kernel or area has dense image.

We allow any class-group homomorphism preserving area. If it also preserves a Chern map,
the comparison negates Chern number on homogeneous supports. Thus raw Floer coefficient
degree `2 c₁` becomes quantum coefficient degree after cochain regrading. On homogeneous pieces
(`TauCeti.NovikovSeries.gradeBy`): the comparison sends quantum series of degree `k`, where `q^A`
has degree `2 c(A)`, to Floer series of raw degree `-k`
(`coefficientComparison_mem_gradeBy_two_smul`, and `periodGroupComparison_mem_gradeBy_degree`
for the joint-period quotient with its degree `PeriodGroup.degree`), which is cochain coefficient
degree `k`. For an injective class map it also reflects degrees
(`coefficientComparison_mem_gradeBy_iff`).

For a quotient by any subgroup of the joint area/Chern kernel, use the descended area and Chern
homomorphisms.
`periodGroupComparison` specializes to the quotient by the entire joint kernel. In that case
two monomials with the same nonzero coefficient become equal exactly when their areas and
Chern numbers agree. No individual quantum invariant is assumed to descend without summation.
If the target class group is trivial, the comparison sends a series to the sum of all of its
coefficients (`coeff_zero_coefficientComparison_of_subsingleton`).

The same pushforward compares Novikov series with coefficients in a graded module `V`, such as
the state module `V ⊗̂ Λ_ω` of quantum cohomology with `V` the cohomology of the target, with
their Floer counterparts. In quantum cohomology `q^A v` has degree `deg v + 2 c₁(A)`. In the
cochain grading `C^k = CF_(n-k)` the monomial `e^γ v` has degree `deg v - 2 c₁(γ)`, since the raw
degree `2 c₁(γ)` of `e^γ` enters `n - μ` with the opposite sign. So `q^A v ↦ e^(-q A) v`
preserves the total degree (`TauCeti.Floer.map_neg_mem_gradeByCoeff`), whereas `q^A v ↦ e^(q A) v`
would change it by `-4 c₁(A)` (`TauCeti.Floer.single_mem_gradeByCoeff_add_iff`).

For a class `A` of positive area the comparison sends the quantum geometric series
`∑ₖ r q^(k A)` to the Floer geometric series `∑ₖ r e^(-k q A)`
(`coefficientComparison_geometric`), whose terms have valuations `k ω(A)` tending to infinity.
This is why the Floer valuation is `-Ω`: the quantum corrections in the multiples of a class of
positive area land in the Floer Novikov ring.

The construction reuses `NovikovSeries.mapRingHom`; no augmentation at `q = 1` is involved.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the Novikov
  coefficient conventions in the chapter on quantum cohomology.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovSeries

variable {R S Γ : Type*}

section Comparison

variable [AddMonoid S] [AddCommGroup Γ]
  {ω : S →+ ℝ} {Ω : Γ →+ ℝ}

section Semiring

variable [Semiring R] (q : S →+ Γ) (hω : ∀ A, Ω (q A) = ω A)

/-- The completed coefficient comparison `q^A ↦ e^(-q A)`, with source period `ω` and
target period `-Ω`. Area preservation makes it a unital ring homomorphism. -/
def coefficientComparison : NovikovSeries R S ω →+* NovikovSeries R Γ (-Ω) :=
  mapRingHom (RingHom.id R) (-q) ⟨1, one_pos, period_rescale_neg hω⟩

/-- The comparison is the existing finite-fibre Novikov pushforward along negative class
projection. -/
theorem coefficientComparison_apply (a : NovikovSeries R S ω) :
    coefficientComparison q hω a =
      map (RingHom.id R : R →+ R) (-q) ⟨1, one_pos, period_rescale_neg hω⟩ a := by
  rw [coefficientComparison, mapRingHom_apply]

/-- The comparison sends a quantum monomial to its negatively indexed Floer monomial. -/
@[simp]
theorem coefficientComparison_single (A : S) (r : R) :
    coefficientComparison q hω (single A r) = single (-q A) r := by
  simp [coefficientComparison]

/-- A coefficient of the comparison is the finite sum over its supported fibre. -/
theorem coeff_coefficientComparison (a : NovikovSeries R S ω) (γ : Γ) :
    (coefficientComparison q hω a).coeff γ =
      ∑ A ∈ (finite_support_inter_preimage_singleton (N' := -Ω) a (φ := -q)
        ⟨1, one_pos, period_rescale_neg hω⟩ γ).toFinset, a.coeff A := by
  classical
  rw [coefficientComparison_apply]
  apply coeff_map_eq_sum (RingHom.id R : R →+ R) (-q) _ a
  · exact fun A hA => (Set.Finite.mem_toFinset _).2 hA
  · intro A hA
    exact ((Set.Finite.mem_toFinset _).1 hA).2

/-- **Over a trivial target class group the comparison is the total count.** The comparison
sends `∑_A N_A q^A` to `∑_A N_A`, a finite sum by
`TauCeti.NovikovSeries.finite_support_of_bddAbove_image`, since every class has zero area:
`ω A = Ω (q A) = 0`. -/
theorem coeff_zero_coefficientComparison_of_subsingleton [Subsingleton Γ]
    (a : NovikovSeries R S ω) :
    (coefficientComparison q hω a).coeff 0 = ∑ᶠ A, a.coeff A := by
  have h : (-q) ⁻¹' {0} = Set.univ := Set.eq_univ_of_forall fun A => Subsingleton.elim _ _
  rw [coefficientComparison_apply, coeff_map, h, finsum_mem_univ]
  simp only [AddMonoidHom.coe_ofClass, RingHom.id_apply]

/-- No new support classes appear except images under negative class projection. -/
theorem support_coefficientComparison_subset (a : NovikovSeries R S ω) :
    (coefficientComparison q hω a).support ⊆ (-q) '' a.support := by
  rw [coefficientComparison_apply]
  exact support_map_subset _ _ _ a

/-- A quotient of class groups gives a surjective comparison, without a finite-kernel
assumption. Each target series can be lifted using one representative of each exponent. -/
theorem coefficientComparison_surjective (hq : Function.Surjective q) :
    Function.Surjective (coefficientComparison (R := R) q hω) := by
  intro b
  obtain ⟨a, ha⟩ := map_surjective (RingHom.id R : R →+ R) (-q)
    (N := ω) (N' := -Ω) ⟨1, one_pos, period_rescale_neg hω⟩
    Function.surjective_id (neg_surjective.comp hq) b
  exact ⟨a, (coefficientComparison_apply q hω a).trans ha⟩

/-- An injective map of class groups gives an injective comparison: the coefficient of the
comparison at `-q A` is the coefficient at `A`. -/
theorem coefficientComparison_injective (hq : Function.Injective q) :
    Function.Injective (coefficientComparison (R := R) q hω) := fun a b hab =>
  map_injective (RingHom.id R : R →+ R) (-q) ⟨1, one_pos, period_rescale_neg hω⟩
    Function.injective_id (fun _ _ h => hq (neg_injective h)) <| by
      rwa [← coefficientComparison_apply, ← coefficientComparison_apply]

/-- If source and target Chern maps agree under class projection, the comparison negates the
Chern number of a homogeneous support. -/
theorem chern_support_coefficientComparison (c : S →+ ℤ) (c' : Γ →+ ℤ)
    (hc : ∀ A, c' (q A) = c A) {k : ℤ} {a : NovikovSeries R S ω}
    (ha : ∀ A ∈ a.support, c A = k) :
    ∀ γ ∈ (coefficientComparison q hω a).support, c' γ = -k := by
  intro γ hγ
  obtain ⟨A, hA, rfl⟩ := support_coefficientComparison_subset q hω a hγ
  simp [hc A, ha A hA]

/-- **The comparison preserves homogeneous pieces.** If a degree `f'` on the Floer classes takes
the value `f A` at the image `-q A` of each class `A`, the comparison sends quantum series of
degree `i` for `f` to Floer series of degree `i` for `f'`. -/
theorem coefficientComparison_mem_gradeBy {ι : Type*} {f : S → ι} {f' : Γ → ι}
    (hf : ∀ A, f' (-q A) = f A) {i : ι} {a : NovikovSeries R S ω}
    (ha : a ∈ gradeBy R ω f i) : coefficientComparison q hω a ∈ gradeBy R (-Ω) f' i := by
  rw [coefficientComparison_apply]
  exact map_mem_gradeBy _ (-q) _ hf ha

/-- For an injective class map the comparison also reflects homogeneous pieces. -/
theorem coefficientComparison_mem_gradeBy_iff (hq : Function.Injective q) {ι : Type*}
    {f : S → ι} {f' : Γ → ι} (hf : ∀ A, f' (-q A) = f A) {i : ι} {a : NovikovSeries R S ω} :
    coefficientComparison q hω a ∈ gradeBy R (-Ω) f' i ↔ a ∈ gradeBy R ω f i := by
  rw [coefficientComparison_apply]
  exact map_mem_gradeBy_iff _ (-q) _ Function.injective_id
    (fun _ _ h => hq (neg_injective h)) hf

/-- **Quantum degree becomes raw Floer degree with the opposite sign.** If the Chern maps agree
under the class map, the comparison sends quantum series of degree `k`, where `q^A` has degree
`2 c(A)`, to Floer series of raw degree `-k`, where `e^γ` has degree `2 c'(γ)`. In the cochain
grading `C^k = CF_(n-k)` a coefficient of raw degree `-k` raises the cochain degree by `k`, so the
comparison preserves degrees for the quantum and the cochain gradings. -/
theorem coefficientComparison_mem_gradeBy_two_smul (c : S →+ ℤ) (c' : Γ →+ ℤ)
    (hc : ∀ A, c' (q A) = c A) {k : ℤ} {a : NovikovSeries R S ω}
    (ha : a ∈ gradeBy R ω (2 • c : S →+ ℤ) k) :
    coefficientComparison q hω a ∈ gradeBy R (-Ω) (2 • c' : Γ →+ ℤ) (-k) := by
  refine coefficientComparison_mem_gradeBy q hω (f := Neg.neg ∘ (2 • c : S →+ ℤ))
    (fun A => by simp [hc]) ?_
  rwa [gradeBy_comp_of_injective neg_injective]

section GradedCoefficients

variable {V : Type*} [AddCommMonoid V] [Module R V] {d : S → ℤ} {d' : Γ →+ ℤ}

/-- **The comparison preserves the total degree.** Let `V` be graded by `𝒱`, for instance the
cohomology of the target, and let `d'` be a degree on `Γ` with `d' (q A) = d A`, for instance
twice the first Chern number. A Novikov series with coefficients in `V` of quantum degree `D`,
whose coefficient at `q^A` has degree `D - d A`, goes under `q^A v ↦ e^(-q A) v` to a series of
cochain degree `D`, whose coefficient at `e^γ` has degree `D + d' γ`: the raw degree `d' γ` of
`e^γ` enters the cochain degree `n - μ` with the opposite sign. For `V = R` the map is
`TauCeti.Floer.coefficientComparison` (`TauCeti.Floer.coefficientComparison_apply`). -/
theorem map_neg_mem_gradeByCoeff (hd : ∀ A, d' (q A) = d A) {𝒱 : ℤ → Submodule R V} {D : ℤ}
    {v : NovikovSeries V S ω} (hv : v ∈ NovikovSeries.gradeByCoeff ω 𝒱 d D) :
    map (AddMonoidHom.id V) (-q) ⟨1, one_pos, period_rescale_neg hω⟩ v ∈
      NovikovSeries.gradeByCoeff (-Ω) 𝒱 (fun γ => -d' γ) D :=
  map_mem_gradeByCoeff (fun _ _ hv => hv) _ (fun A => by simp [hd]) hv

open Function in
/-- **The opposite comparison reverses the degree.** In the cochain grading, where `e^γ` has
degree `-δ γ`, a monomial `e^γ v` with `v ≠ 0` of degree `j` has degree `j - δ γ`. For pairwise
disjoint pieces `𝒱` this is `j + δ γ` only when `δ γ = 0`. So under `q^A v ↦ e^(q A) v`, with
`δ (q A) = d A`, the image of `q^A v`, of quantum degree `j + d A`, would have that degree only
when `d A = 0`. -/
theorem single_mem_gradeByCoeff_add_iff {δ : Γ → ℤ} {N : Γ →+ ℝ} {𝒱 : ℤ → Submodule R V}
    (h𝒱 : Pairwise (Disjoint on 𝒱)) {j : ℤ} {v : V} (hv : v ∈ 𝒱 j) (hv₀ : v ≠ 0) (γ : Γ) :
    (single γ v : NovikovSeries V Γ N) ∈
        NovikovSeries.gradeByCoeff N 𝒱 (fun γ => -δ γ) (j + δ γ) ↔ δ γ = 0 := by
  rw [single_mem_gradeByCoeff_iff_of_mem h𝒱 hv hv₀]
  omega

end GradedCoefficients

end Semiring

section Ring

variable [Ring R] (q : S →+ Γ) (hω : ∀ A, Ω (q A) = ω A)

/-- The coefficient comparison is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_coefficientComparison :
    Continuous (coefficientComparison (R := R) q hω) :=
  continuous_mapRingHom _ _ _

/-- The comparison preserves every energy cutoff, including all reference-class constants
that have already been incorporated into that cutoff. -/
theorem coefficientComparison_mem_periodFiltration {C : ℝ} {a : NovikovSeries R S ω}
    (ha : a ∈ periodFiltration R ω C) :
    coefficientComparison q hω a ∈ periodFiltration R (-Ω) C := by
  rw [coefficientComparison_apply]
  simpa only [one_mul] using map_mem_periodFiltration (RingHom.id R : R →+ R) (-q)
    (N' := -Ω) _ zero_le_one (period_rescale_neg hω) ha

end Ring

end Comparison

section Geometric

variable [AddGroup S] [AddCommGroup Γ] {ω : S →+ ℝ} {Ω : Γ →+ ℝ} [Semiring R] (q : S →+ Γ)
  (hω : ∀ A, Ω (q A) = ω A)

/-- **The comparison of a geometric series.** A class `A` of positive area gives the quantum
geometric series `∑ₖ r q^(k A)`, and the comparison sends it to the Floer geometric series
`∑ₖ r e^(-k q A)`, whose exponent `-q A` has positive valuation `ω A`. So the quantum corrections
in the multiples of a class of positive area land in the Floer Novikov ring. -/
@[simp]
theorem coefficientComparison_geometric {A : S} (hA : 0 < ω A) (r : R) :
    coefficientComparison q hω (geometric ω hA r) =
      geometric (-Ω) (h := -q A) (by simpa [hω] using hA) r := by
  rw [coefficientComparison_apply, map_geometric]
  simp only [AddMonoidHom.neg_apply, RingHom.toAddMonoidHom_id, AddMonoidHom.id_apply]

end Geometric

section PeriodGroup

variable [AddCommGroup S] (ω : S →+ ℝ) (c : S →+ ℤ)

/-- Descent from a common class group to the Floer joint-period quotient, with the sign
change `q^A ↦ e^(-[A])` and finite summation of all coefficients having that image. -/
def periodGroupComparison [Semiring R] :
    NovikovSeries R S ω →+* NovikovSeries R (PeriodGroup ω c) (-PeriodGroup.area ω c) :=
  coefficientComparison (QuotientAddGroup.mk' (ω.prod c).ker) (PeriodGroup.area_mk ω c)

/-- The joint-period comparison is the signed coefficient comparison for the canonical
quotient projection. This gives access to its finite coefficient-sum and support formulas. -/
theorem periodGroupComparison_apply [Semiring R] (a : NovikovSeries R S ω) :
    periodGroupComparison ω c a =
      coefficientComparison (QuotientAddGroup.mk' (ω.prod c).ker)
        (PeriodGroup.area_mk ω c) a :=
  (rfl)

/-- The joint-period comparison sends `q^A` to `e^(-[A])`. -/
@[simp]
theorem periodGroupComparison_single [Semiring R] (A : S) (r : R) :
    periodGroupComparison ω c (single A r) = single (-(A : PeriodGroup ω c)) r :=
  coefficientComparison_single _ _ _ _

/-- Descent to the joint-period quotient is surjective even when area alone fails to
separate classes. -/
theorem periodGroupComparison_surjective [Semiring R] :
    Function.Surjective (periodGroupComparison (R := R) ω c) :=
  coefficientComparison_surjective _ _ (QuotientAddGroup.mk'_surjective _)

/-- Descent to the joint-period quotient is injective when area and first Chern number jointly
separate classes, that is, when only the zero class has vanishing area and Chern number. -/
theorem periodGroupComparison_injective [Semiring R] (h : Disjoint ω.ker c.ker) :
    Function.Injective (periodGroupComparison (R := R) ω c) :=
  coefficientComparison_injective _ _ <| (injective_iff_map_eq_zero _).2 fun s hs => by
    rw [← AddSubgroup.mem_bot, ← h.eq_bot, ← AddMonoidHom.ker_prod]
    exact (QuotientAddGroup.eq_zero_iff s).1 hs

/-- Descent to the joint-period quotient is bijective when area and first Chern number jointly
separate classes. -/
theorem periodGroupComparison_bijective [Semiring R] (h : Disjoint ω.ker c.ker) :
    Function.Bijective (periodGroupComparison (R := R) ω c) :=
  ⟨periodGroupComparison_injective ω c h, periodGroupComparison_surjective ω c⟩

/-- **The joint-period comparison negates degrees.** It sends quantum series of degree `k`, where
`q^A` has degree `2 c(A)`, to Floer series of raw degree `-k`, where `e^γ` has degree
`PeriodGroup.degree ω c γ = 2 c(γ)`; that is, of cochain coefficient degree `k`. -/
theorem periodGroupComparison_mem_gradeBy_degree [Semiring R] {k : ℤ} {a : NovikovSeries R S ω}
    (ha : a ∈ gradeBy R ω (2 • c : S →+ ℤ) k) :
    periodGroupComparison ω c a ∈
      gradeBy R (-PeriodGroup.area ω c) (PeriodGroup.degree ω c) (-k) := by
  rw [PeriodGroup.degree_eq_two_smul_chern]
  exact coefficientComparison_mem_gradeBy_two_smul _ (PeriodGroup.area_mk ω c) c
    (PeriodGroup.chern ω c) (PeriodGroup.chern_mk ω c) ha

/-- The joint-period comparison is continuous for the energy topologies. -/
@[fun_prop]
theorem continuous_periodGroupComparison [Ring R] :
    Continuous (periodGroupComparison (R := R) ω c) :=
  continuous_coefficientComparison _ _

/-- Monomial descent identifies precisely the joint periods, retaining equal-area classes
of different Chern number. The coefficient is assumed nonzero. -/
theorem periodGroupComparison_single_eq_iff [Semiring R] {r : R} (hr : r ≠ 0) (A B : S) :
    periodGroupComparison ω c (single A r) = periodGroupComparison ω c (single B r) ↔
      ω A = ω B ∧ c A = c B := by
  rw [periodGroupComparison_single, periodGroupComparison_single]
  constructor
  · intro h
    have hs := congrArg NovikovSeries.support h
    rw [support_single_of_ne hr, support_single_of_ne hr, Set.singleton_eq_singleton_iff,
      neg_inj] at hs
    exact PeriodGroup.mk_eq_mk_iff.1 hs
  · intro h
    rw [PeriodGroup.mk_eq_mk_iff.2 h]

end PeriodGroup

end TauCeti.Floer
