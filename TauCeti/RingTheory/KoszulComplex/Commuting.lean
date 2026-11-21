/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The cohomological Koszul complex of a commuting family of endomorphisms

Let `D : ι → Module.End R M` be a family of endomorphisms of a module `M`, indexed by a linearly
ordered type `ι`. A Koszul cochain is a family `ω : Finset ι → M`, the coefficient `ω J` being
the coefficient of the exterior monomial `e_J = e_{j₁} ∧ ⋯ ∧ e_{j_q}` (`j₁ < ⋯ < j_q`); the
cochains of degree `q` are those supported on index sets of cardinality `q`
(`TauCeti.koszulCochains`). The Koszul differential (`TauCeti.koszulCochainDifferential`) is
`d = ∑ⱼ e_j ∧ D j`, that is

`(d ω) J = ∑_{j ∈ J} (-1) ^ #{i ∈ J | i < j} • D j (ω (J.erase j))`,

the sign being the shuffle sign `TauCeti.ExteriorAlgebra.basisEraseSign j J` that moves `j` to
the front of `J`. It raises the degree by one, and it squares to zero as soon as the `D j`
commute pairwise (`TauCeti.koszulCochainDifferential_koszulCochainDifferential`), since the two
orders of applying `D j` and `D k` carry opposite signs. When the `D j` are multiplications by
elements `x_j` of a commutative ring this is the cohomological Koszul complex `K^•(x; M)`; in
general it is the Koszul complex of `M` regarded as a module over the polynomial ring through
the commuting operators.

The main example is the twisted de Rham complex `(Ω^•(T), d + dφ ∧)` of a split torus `T`,
written in the basis `dlog x_J` of differential forms: it is the Koszul complex of the twisted
Euler operators `x_j ∂/∂x_j + x_j ∂φ/∂x_j` on the Laurent polynomial ring.

For a finite index type, the top-degree cochains are all cocycles, and the top cohomology is
the cokernel `M ⧸ ∑ᵢ range (D i)` of the family (`TauCeti.koszulTopCohomologyEquiv`).

## Main definitions

* `TauCeti.koszulCochains R ι M q`: the cochains of degree `q`.
* `TauCeti.koszulCochainDifferential D`: the Koszul differential.
* `TauCeti.koszulCocycles D q` and `TauCeti.koszulCoboundaries D q`: the cocycles and the
  coboundaries of degree `q`.
* `TauCeti.koszulTopCohomologyEquiv D`: the top cohomology is `M ⧸ ∑ᵢ range (D i)`.

## Main results

* `TauCeti.koszulCochainDifferential_mem_koszulCochains`: `d` raises the degree by one.
* `TauCeti.koszulCochainDifferential_koszulCochainDifferential`: `d ∘ d = 0` for a commuting
  family.
* `TauCeti.koszulCoboundaries_le_koszulCocycles`: coboundaries are cocycles.
* `TauCeti.map_koszulCoboundaries_card`: the top-degree coboundaries are the families whose
  coefficient on the full index set lies in `∑ᵢ range (D i)`.

## References

* [The Stacks Project, Tag 0621](https://stacks.math.columbia.edu/tag/0621), for the Koszul
  complex of a sequence of elements.
* A. Adolphson and S. Sperber, *On twisted de Rham cohomology*, Nagoya Math. J. 146 (1997),
  for the twisted de Rham complex of a torus as the Koszul complex of the twisted Euler
  operators.
-/

public section

open Finset TauCeti.ExteriorAlgebra

namespace TauCeti

section Semiring

variable (R ι M : Type*) [Semiring R] [AddCommGroup M] [Module R M]

/-- The **Koszul cochains of degree `q`**: the families `ω : Finset ι → M` supported on index
sets of cardinality `q`. The coefficient `ω J` is that of the exterior monomial `e_J`. -/
def koszulCochains (q : ℕ) : Submodule R (Finset ι → M) where
  carrier := {ω | ∀ J : Finset ι, #J ≠ q → ω J = 0}
  add_mem' hω hω' J hJ := by simp [hω J hJ, hω' J hJ]
  zero_mem' _ _ := rfl
  smul_mem' r ω hω J hJ := by simp [hω J hJ]

variable {R ι M}

@[simp]
theorem mem_koszulCochains {q : ℕ} {ω : Finset ι → M} :
    ω ∈ koszulCochains R ι M q ↔ ∀ J : Finset ι, #J ≠ q → ω J = 0 :=
  Iff.rfl

/-- Above the number of indices there are no nonzero cochains. -/
theorem koszulCochains_eq_bot [Fintype ι] {q : ℕ} (hq : Fintype.card ι < q) :
    koszulCochains R ι M q = ⊥ := by
  refine eq_bot_iff.mpr fun ω hω ↦ (Submodule.mem_bot R).mpr
    (funext fun J ↦ mem_koszulCochains.mp hω J ?_)
  have := J.card_le_univ
  omega

variable [LinearOrder ι] (D : ι → Module.End R M)

/-- The **Koszul differential** `d = ∑ⱼ e_j ∧ D j` of a family of endomorphisms `D`, on the
cochains `Finset ι → M`: the coefficient of `J` in `d ω` is
`∑_{j ∈ J} (-1) ^ #{i ∈ J | i < j} • D j (ω (J.erase j))`, the sign
`TauCeti.ExteriorAlgebra.basisEraseSign j J` being the shuffle sign of `e_j ∧ e_{J.erase j}`. -/
noncomputable def koszulCochainDifferential : Module.End R (Finset ι → M) :=
  LinearMap.pi fun J ↦ ∑ j ∈ J, basisEraseSign j J • (D j ∘ₗ LinearMap.proj (J.erase j))

theorem koszulCochainDifferential_apply (ω : Finset ι → M) (J : Finset ι) :
    koszulCochainDifferential D ω J = ∑ j ∈ J, basisEraseSign j J • D j (ω (J.erase j)) := by
  simp [koszulCochainDifferential]

/-- The Koszul differential raises the degree of a cochain by one. -/
theorem koszulCochainDifferential_mem_koszulCochains {q : ℕ} {ω : Finset ι → M}
    (hω : ω ∈ koszulCochains R ι M q) :
    koszulCochainDifferential D ω ∈ koszulCochains R ι M (q + 1) := by
  rw [mem_koszulCochains] at hω ⊢
  intro J hJ
  rw [koszulCochainDifferential_apply]
  refine sum_eq_zero fun j hj ↦ ?_
  have := card_pos.mpr ⟨j, hj⟩
  rw [hω (J.erase j) (by rw [card_erase_of_mem hj]; omega), map_zero, smul_zero]

/-- Removing `j` from `J` removes it from the indices below `k` exactly when `j < k`. -/
private theorem card_filter_lt_erase_add {J : Finset ι} {j : ι} (hj : j ∈ J) (k : ι) :
    #{i ∈ J.erase j | i < k} + (if j < k then 1 else 0) = #{i ∈ J | i < k} := by
  rw [filter_erase]
  split_ifs with hjk
  · exact card_erase_add_one (mem_filter.mpr ⟨hj, hjk⟩)
  · rw [add_zero, erase_eq_of_notMem]
    simp [hjk]

/-- The two orders of removing distinct indices `j` and `k` from `J` carry opposite products of
shuffle signs. -/
private theorem basisEraseSign_mul_basisEraseSign_erase {J : Finset ι} {j k : ι} (hj : j ∈ J)
    (hk : k ∈ J) (hjk : j ≠ k) :
    basisEraseSign j J * basisEraseSign k (J.erase j) =
      -(basisEraseSign k J * basisEraseSign j (J.erase k)) := by
  have h₁ := card_filter_lt_erase_add hj k
  have h₂ := card_filter_lt_erase_add hk j
  simp only [basisEraseSign_eq_neg_one_pow_card_filter_lt]
  rcases hjk.lt_or_gt with h | h
  · simp only [h, h.not_gt, ite_true, ite_false, add_zero] at h₁ h₂
    rw [← h₁, h₂]
    ext
    push_cast
    ring
  · simp only [h, h.not_gt, ite_true, ite_false, add_zero] at h₁ h₂
    rw [← h₂, h₁]
    ext
    push_cast
    ring

/-- **The Koszul differential of a commuting family squares to zero.** Only distinct members of
the family need to commute. -/
theorem koszulCochainDifferential_koszulCochainDifferential
    (hD : Pairwise fun i j ↦ Commute (D i) (D j)) (ω : Finset ι → M) :
    koszulCochainDifferential D (koszulCochainDifferential D ω) = 0 := by
  funext J
  simp only [koszulCochainDifferential_apply, map_sum, map_zsmul_unit, smul_sum, smul_smul,
    Pi.zero_apply]
  rw [sum_sigma']
  -- The terms indexed by `(j, k)` and `(k, j)` cancel.
  refine sum_involution (fun p _ ↦ ⟨p.2, p.1⟩) (fun ⟨j, k⟩ hp ↦ ?_) (fun ⟨j, k⟩ hp _ h ↦ ?_)
    (fun ⟨j, k⟩ hp ↦ ?_) (fun _ _ ↦ rfl)
  · simp only [mem_sigma, mem_erase] at hp
    have hcomm : D j (D k (ω ((J.erase j).erase k))) = D k (D j (ω ((J.erase k).erase j))) := by
      rw [erase_right_comm]
      exact congr($((hD hp.2.1.symm).eq) _)
    dsimp only
    rw [hcomm, basisEraseSign_mul_basisEraseSign_erase hp.1 hp.2.2 hp.2.1.symm, Units.neg_smul,
      neg_add_cancel]
  · simp only [mem_sigma, mem_erase] at hp
    exact hp.2.1 (congrArg Sigma.fst h)
  · simp only [mem_sigma, mem_erase] at hp ⊢
    exact ⟨hp.2.2, hp.2.1.symm, hp.1⟩

/-- The **Koszul cocycles of degree `q`**: the cochains of degree `q` killed by the Koszul
differential. -/
noncomputable def koszulCocycles (q : ℕ) : Submodule R (Finset ι → M) :=
  koszulCochains R ι M q ⊓ LinearMap.ker (koszulCochainDifferential D)

@[simp]
theorem mem_koszulCocycles {q : ℕ} {ω : Finset ι → M} :
    ω ∈ koszulCocycles D q ↔
      ω ∈ koszulCochains R ι M q ∧ koszulCochainDifferential D ω = 0 :=
  Iff.rfl

/-- The **Koszul coboundaries of degree `q`**: the images of the cochains of degree `q - 1` under
the Koszul differential, and zero in degree `0`. -/
noncomputable def koszulCoboundaries : ℕ → Submodule R (Finset ι → M)
  | 0 => ⊥
  | q + 1 => (koszulCochains R ι M q).map (koszulCochainDifferential D)

@[simp]
theorem koszulCoboundaries_zero : koszulCoboundaries D 0 = ⊥ :=
  (rfl)

theorem koszulCoboundaries_succ (q : ℕ) :
    koszulCoboundaries D (q + 1) = (koszulCochains R ι M q).map (koszulCochainDifferential D) :=
  (rfl)

theorem koszulCoboundaries_le_koszulCochains (q : ℕ) :
    koszulCoboundaries D q ≤ koszulCochains R ι M q := by
  cases q with
  | zero => exact bot_le
  | succ q =>
    rintro _ ⟨ω, hω, rfl⟩
    exact koszulCochainDifferential_mem_koszulCochains D hω

/-- For a commuting family, every Koszul coboundary is a cocycle. -/
theorem koszulCoboundaries_le_koszulCocycles (hD : Pairwise fun i j ↦ Commute (D i) (D j))
    (q : ℕ) : koszulCoboundaries D q ≤ koszulCocycles D q := by
  refine le_inf (koszulCoboundaries_le_koszulCochains D q) ?_
  cases q with
  | zero => exact bot_le
  | succ q =>
    rintro _ ⟨ω, -, rfl⟩
    exact koszulCochainDifferential_koszulCochainDifferential D hD ω

section Fintype

variable [Fintype ι]

/-- In the top degree every cochain is a cocycle. -/
theorem koszulCocycles_card : koszulCocycles D (Fintype.card ι) =
    koszulCochains R ι M (Fintype.card ι) := by
  refine inf_eq_left.mpr fun ω hω ↦ ?_
  have h := koszulCochainDifferential_mem_koszulCochains D hω
  rw [koszulCochains_eq_bot (Nat.lt_succ_self _), Submodule.mem_bot] at h
  exact h

/-- **The top-degree Koszul coboundaries**: their coefficients on the full index set are exactly
the elements of `∑ᵢ range (D i)`. -/
theorem map_koszulCoboundaries_card :
    (koszulCoboundaries D (Fintype.card ι)).map (LinearMap.proj (univ : Finset ι)) =
      ⨆ i, LinearMap.range (D i) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Fintype.card_eq_zero]
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card ι = q + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  rw [hq, koszulCoboundaries_succ]
  refine le_antisymm ?_ (iSup_le fun j ↦ ?_)
  · rintro _ ⟨_, ⟨ω, -, rfl⟩, rfl⟩
    rw [LinearMap.proj_apply, koszulCochainDifferential_apply]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [← map_zsmul_unit]
    exact Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ _)
  · rintro _ ⟨m, rfl⟩
    have hω : Pi.single (univ.erase j) (basisEraseSign j univ • m) ∈ koszulCochains R ι M q :=
      mem_koszulCochains.mpr fun J hJ ↦ Pi.single_eq_of_ne (fun h ↦ hJ (by
        rw [h, card_erase_of_mem (mem_univ j), card_univ, hq, Nat.add_sub_cancel])) _
    refine ⟨_, ⟨_, hω, rfl⟩, ?_⟩
    rw [LinearMap.proj_apply, koszulCochainDifferential_apply,
      sum_eq_single j (fun k _ hkj ↦ ?_) (fun h ↦ (h (mem_univ j)).elim)]
    · rw [Pi.single_eq_same, map_zsmul_unit, smul_smul, Int.units_mul_self, one_smul]
    · rw [Pi.single_eq_of_ne (fun h ↦ hkj ((erase_inj _ (mem_univ k)).mp h)), map_zero,
        smul_zero]

end Fintype

end Semiring

section Ring

variable {R ι M : Type*} [Ring R] [AddCommGroup M] [Module R M] [LinearOrder ι] [Fintype ι]
  (D : ι → Module.End R M)

/-- A top-degree cocycle is determined by its coefficient on the full index set. -/
private noncomputable def koszulCocyclesCardEquiv :
    koszulCocycles D (Fintype.card ι) ≃ₗ[R] M where
  toFun ω := ω.val univ
  invFun m := ⟨Pi.single univ m, by
    rw [koszulCocycles_card]
    exact mem_koszulCochains.mpr fun J hJ ↦
      Pi.single_eq_of_ne (fun h ↦ hJ (by rw [h, card_univ])) _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ω := by
    obtain ⟨ω, hω⟩ := ω
    rw [koszulCocycles_card] at hω
    refine Subtype.ext (funext fun J ↦ ?_)
    dsimp only
    by_cases hJ : J = univ
    · subst hJ
      exact Pi.single_eq_same _ _
    · rw [Pi.single_eq_of_ne hJ,
        mem_koszulCochains.mp hω J fun h ↦ hJ (card_eq_iff_eq_univ J |>.mp h)]
  right_inv m := Pi.single_eq_same _ _

/-- **The top Koszul cohomology is the cokernel of the family**: for a finite index type, the
quotient of the top-degree cocycles by the coboundaries is `M ⧸ ∑ᵢ range (D i)`, through the
coefficient on the full index set. No commutation hypothesis is needed. -/
noncomputable def koszulTopCohomologyEquiv :
    (koszulCocycles D (Fintype.card ι) ⧸ (koszulCoboundaries D (Fintype.card ι)).comap
        (koszulCocycles D (Fintype.card ι)).subtype) ≃ₗ[R]
      M ⧸ ⨆ i, LinearMap.range (D i) :=
  Submodule.Quotient.equiv _ _ (koszulCocyclesCardEquiv D) <| by
    rw [← map_koszulCoboundaries_card D]
    ext m
    constructor
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω.val, hω, rfl⟩
    · rintro ⟨ω, hω, rfl⟩
      have hc : ω ∈ koszulCocycles D (Fintype.card ι) := by
        rw [koszulCocycles_card]
        exact koszulCoboundaries_le_koszulCochains D _ hω
      exact ⟨⟨ω, hc⟩, hω, rfl⟩

@[simp]
theorem koszulTopCohomologyEquiv_mk (ω : koszulCocycles D (Fintype.card ι)) :
    koszulTopCohomologyEquiv D (Submodule.Quotient.mk ω) = Submodule.Quotient.mk (ω.val univ) :=
  (rfl)

end Ring

end TauCeti
