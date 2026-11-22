/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Basic

/-!
# Permutation-invariant polynomial subalgebras and orbit-sum bases

For a subgroup `G` of `Equiv.Perm σ` acting on `MvPolynomial σ R` by variable renaming
`MvPolynomial.rename`, the `G`-invariant polynomials form an `R`-subalgebra
`MvPolynomial.permInvariantSubalgebra G R`, generalizing `MvPolynomial.symmetricSubalgebra σ R`
(which is the case `G = ⊤`).

When `G` is finite, each `G`-orbit on exponent vectors `σ →₀ ℕ` (via `Finsupp.equivMapDomain`) is
finite, and summing the corresponding monic monomials produces the orbit sum
`MvPolynomial.orbitSum G R d`. These orbit sums depend only on the `G`-orbit of `d` and form an
`R`-module basis `MvPolynomial.orbitSumBasis G R` of `MvPolynomial.permInvariantSubalgebra G R`
over an arbitrary commutative semiring `R` (in particular, in every characteristic).

For any monomial order `m` on `σ →₀ ℕ`, an exponent `d` is maximal in its `G`-orbit for `m` if and
only if it is the `m`-leading exponent of a nonzero `G`-invariant polynomial (witnessed by
`orbitSum G R d`, which is monic). Thus `m.leadingExponents (permInvariantSubalgebra G R)` is
precisely the monoid of `m`-maximal orbit representatives.

## Main definitions

* `MvPolynomial.permInvariantSubalgebra`: the subalgebra of `G`-invariant polynomials.
* `MvPolynomial.permOrbitRel`: the orbit equivalence relation of `G` on `σ →₀ ℕ`.
* `MvPolynomial.permOrbit`: the `G`-orbit of an exponent vector `d : σ →₀ ℕ`.
* `MvPolynomial.orbitSum`: the sum of monic monomials in the `G`-orbit of `d`.
* `MvPolynomial.orbitSumQuot`: the orbit sum indexed by `Quotient (permOrbitRel G)`.
* `MvPolynomial.orbitSumBasis`: the `R`-basis of `permInvariantSubalgebra G R` by orbit sums.

## Main results

* `MvPolynomial.mem_permInvariantSubalgebra_iff_coeff`: a polynomial is `G`-invariant if and only
  if its coefficients are constant along `G`-orbits of exponents.
* `MonomialOrder.degree_orbitSum_of_forall_le` and
  `MonomialOrder.leadingCoeff_orbitSum_of_forall_le`: an orbit sum indexed by an `m`-maximal
  exponent is monic of that degree.
* `MonomialOrder.mem_leadingExponents_permInvariantSubalgebra_iff`: characterization of the
  leading-exponent monoid of `permInvariantSubalgebra G R`.
-/

public section

open Equiv

namespace MvPolynomial

section Subalgebra

variable {σ R : Type*} [CommSemiring R]

/-- The `R`-subalgebra of polynomials in `MvPolynomial σ R` invariant under variable permutations
from a subgroup `G ≤ Equiv.Perm σ`. -/
def permInvariantSubalgebra (G : Subgroup (Perm σ)) (R : Type*) [CommSemiring R] :
    Subalgebra R (MvPolynomial σ R) where
  carrier := {p | ∀ g ∈ G, rename g p = p}
  algebraMap_mem' r g _ := rename_C g r
  mul_mem' ha hb g hg := by rw [map_mul, ha g hg, hb g hg]
  add_mem' ha hb g hg := by rw [map_add, ha g hg, hb g hg]

@[simp]
theorem mem_permInvariantSubalgebra {G : Subgroup (Perm σ)} {p : MvPolynomial σ R} :
    p ∈ permInvariantSubalgebra G R ↔ ∀ g ∈ G, rename g p = p :=
  Iff.rfl

@[simp]
theorem permInvariantSubalgebra_top :
    permInvariantSubalgebra (⊤ : Subgroup (Perm σ)) R = symmetricSubalgebra σ R := by
  ext p; simp [mem_symmetricSubalgebra, IsSymmetric]

@[simp]
theorem permInvariantSubalgebra_bot :
    permInvariantSubalgebra (⊥ : Subgroup (Perm σ)) R = ⊤ := by
  ext p; simp [rename_id]

theorem permInvariantSubalgebra_antitone {G H : Subgroup (Perm σ)} (h : G ≤ H) :
    permInvariantSubalgebra H R ≤ permInvariantSubalgebra G R :=
  fun _ hp g hg => hp g (h hg)

theorem symmetricSubalgebra_le_permInvariantSubalgebra (G : Subgroup (Perm σ)) :
    symmetricSubalgebra σ R ≤ permInvariantSubalgebra G R :=
  permInvariantSubalgebra_top (R := R) ▸ permInvariantSubalgebra_antitone le_top

/-- Renaming a polynomial by a permutation `g` permutes its coefficients by
`Finsupp.equivMapDomain`. -/
@[simp]
theorem coeff_rename_equivMapDomain (g : Perm σ) (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (rename g p).coeff (d.equivMapDomain g) = p.coeff d := by
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact coeff_rename_mapDomain g g.injective p d

/-- A polynomial is `G`-invariant if and only if its coefficients are constant along every
`G`-orbit of exponent vectors. -/
theorem mem_permInvariantSubalgebra_iff_coeff {G : Subgroup (Perm σ)} {p : MvPolynomial σ R} :
    p ∈ permInvariantSubalgebra G R ↔
      ∀ g ∈ G, ∀ d : σ →₀ ℕ, p.coeff (d.equivMapDomain g) = p.coeff d := by
  refine ⟨fun hp g hg d => by rw [← coeff_rename_equivMapDomain g p d, hp g hg], fun h g hg => ?_⟩
  ext e
  have he : e = (e.equivMapDomain g.symm).equivMapDomain g := by
    rw [← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self, Finsupp.equivMapDomain_refl]
  conv_lhs => rw [he]
  rw [coeff_rename_equivMapDomain, ← h g hg (e.equivMapDomain g.symm), ← he]

/-- A polynomial is invariant under a subgroup `G` if and only if it is invariant under a
generating set of `G`. -/
theorem mem_permInvariantSubalgebra_closure_iff {S : Set (Perm σ)} {p : MvPolynomial σ R} :
    p ∈ permInvariantSubalgebra (Subgroup.closure S) R ↔ ∀ g ∈ S, rename g p = p := by
  refine ⟨fun hp g hg => hp g (Subgroup.subset_closure hg), fun h g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => rw [Perm.coe_one, rename_id, AlgHom.id_apply]
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    rw [Perm.coe_mul, ← rename_rename, ih₂, ih₁]
  | inv g _ ih =>
    have h' := congrArg (rename (⇑g⁻¹)) ih
    rw [rename_rename, Perm.inv_def, Equiv.symm_comp_self, rename_id] at h'
    exact h'.symm

end Subalgebra

section OrbitSum

variable {σ : Type*}

/-- The `G`-orbit equivalence relation on exponent vectors `σ →₀ ℕ`, where `d₁ ≈ d₂` when
`d₁.equivMapDomain g = d₂` for some `g ∈ G`. -/
def permOrbitRel (G : Subgroup (Perm σ)) : Setoid (σ →₀ ℕ) where
  r d₁ d₂ := ∃ g ∈ G, d₁.equivMapDomain g = d₂
  iseqv :=
    { refl := fun d => ⟨1, G.one_mem, Finsupp.equivMapDomain_refl d⟩
      symm := by
        rintro d₁ d₂ ⟨g, hg, rfl⟩
        exact ⟨g⁻¹, G.inv_mem hg, by
          rw [← Finsupp.equivMapDomain_trans, Perm.inv_def, Equiv.self_trans_symm,
            Finsupp.equivMapDomain_refl]⟩
      trans := by
        rintro d₁ d₂ d₃ ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩
        exact ⟨g₂ * g₁, G.mul_mem hg₂ hg₁, Finsupp.equivMapDomain_trans g₁ g₂ d₁⟩ }

theorem permOrbitRel_iff {G : Subgroup (Perm σ)} {d₁ d₂ : σ →₀ ℕ} :
    permOrbitRel G d₁ d₂ ↔ ∃ g ∈ G, d₁.equivMapDomain g = d₂ :=
  Iff.rfl

/-- The `G`-orbit of an exponent vector `d : σ →₀ ℕ` under `Finsupp.equivMapDomain`. -/
def permOrbit (G : Subgroup (Perm σ)) (d : σ →₀ ℕ) : Set (σ →₀ ℕ) :=
  {e | ∃ g ∈ G, d.equivMapDomain g = e}

@[simp]
theorem mem_permOrbit_iff {G : Subgroup (Perm σ)} {d e : σ →₀ ℕ} :
    e ∈ permOrbit G d ↔ ∃ g ∈ G, d.equivMapDomain g = e :=
  Iff.rfl

theorem mem_permOrbit_self (G : Subgroup (Perm σ)) (d : σ →₀ ℕ) : d ∈ permOrbit G d :=
  ⟨1, G.one_mem, Finsupp.equivMapDomain_refl d⟩

theorem permOrbit_eq_of_rel {G : Subgroup (Perm σ)} {d₁ d₂ : σ →₀ ℕ}
    (h : permOrbitRel G d₁ d₂) : permOrbit G d₁ = permOrbit G d₂ :=
  Set.ext fun _ => ⟨(permOrbitRel G).trans ((permOrbitRel G).symm h), (permOrbitRel G).trans h⟩

theorem mem_permOrbit_iff_quotient_mk_eq {G : Subgroup (Perm σ)} {d e : σ →₀ ℕ} :
    e ∈ permOrbit G d ↔ Quotient.mk (permOrbitRel G) e = Quotient.mk (permOrbitRel G) d := by
  rw [Quotient.eq]; exact ⟨(permOrbitRel G).symm, (permOrbitRel G).symm⟩

theorem permOrbit_finite (G : Subgroup (Perm σ)) [Finite G] (d : σ →₀ ℕ) :
    (permOrbit G d).Finite := by
  convert Set.finite_range (fun g : G => d.equivMapDomain (g : Perm σ))
  ext e; simp [permOrbit]

variable {R : Type*} [CommSemiring R]

/-- The **orbit sum** of an exponent vector `d : σ →₀ ℕ` for a finite permutation subgroup
`G ≤ Equiv.Perm σ`: the sum of the monic monomials `X^e` as `e` ranges over the `G`-orbit of `d`. -/
noncomputable def orbitSum (G : Subgroup (Perm σ)) [Finite G] (R : Type*) [CommSemiring R]
    (d : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ e ∈ (permOrbit_finite G d).toFinset, monomial e (1 : R)

theorem orbitSum_def (G : Subgroup (Perm σ)) [Finite G] (R : Type*) [CommSemiring R]
    (d : σ →₀ ℕ) :
    orbitSum G R d = ∑ e ∈ (permOrbit_finite G d).toFinset, monomial e (1 : R) :=
  (rfl)

/-- The coefficient of `X^e` in `orbitSum G R d` is `1` if `e` lies in the `G`-orbit of `d`,
and `0` otherwise. -/
theorem coeff_orbitSum (G : Subgroup (Perm σ)) [Finite G] (d e : σ →₀ ℕ)
    [Decidable (e ∈ permOrbit G d)] :
    (orbitSum G R d).coeff e = if e ∈ permOrbit G d then 1 else 0 := by
  classical
  rw [orbitSum_def, coeff_sum]
  simp_rw [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp

/-- The coefficient of `X^e` in `orbitSum G R d` is `1` when `e` lies in the `G`-orbit of `d`. -/
theorem coeff_orbitSum_of_mem (G : Subgroup (Perm σ)) [Finite G] {d e : σ →₀ ℕ}
    (he : e ∈ permOrbit G d) :
    (orbitSum G R d).coeff e = 1 := by
  classical simp [coeff_orbitSum, he]

/-- The coefficient of `X^e` in `orbitSum G R d` is `0` when `e` is outside the `G`-orbit of `d`. -/
theorem coeff_orbitSum_of_notMem (G : Subgroup (Perm σ)) [Finite G] {d e : σ →₀ ℕ}
    (he : e ∉ permOrbit G d) :
    (orbitSum G R d).coeff e = 0 := by
  classical simp [coeff_orbitSum, he]

@[simp]
theorem coeff_orbitSum_self (G : Subgroup (Perm σ)) [Finite G] (d : σ →₀ ℕ) :
    (orbitSum G R d).coeff d = 1 :=
  coeff_orbitSum_of_mem G (mem_permOrbit_self G d)

theorem support_orbitSum (G : Subgroup (Perm σ)) [Finite G] [Nontrivial R] (d : σ →₀ ℕ) :
    (orbitSum G R d).support = (permOrbit_finite G d).toFinset := by
  classical
  ext e
  simp [mem_support_iff, coeff_orbitSum]

theorem orbitSum_ne_zero (G : Subgroup (Perm σ)) [Finite G] [Nontrivial R] (d : σ →₀ ℕ) :
    orbitSum G R d ≠ 0 := fun h => by
  have h1 := coeff_orbitSum_self (R := R) G d
  simp [h] at h1

theorem orbitSum_eq_of_rel (G : Subgroup (Perm σ)) [Finite G] {d₁ d₂ : σ →₀ ℕ}
    (h : permOrbitRel G d₁ d₂) : orbitSum G R d₁ = orbitSum G R d₂ := by
  classical
  ext e
  simp [coeff_orbitSum, permOrbit_eq_of_rel h]

@[simp]
theorem orbitSum_equivMapDomain (G : Subgroup (Perm σ)) [Finite G] {g : Perm σ} (hg : g ∈ G)
    (d : σ →₀ ℕ) :
    orbitSum G R (d.equivMapDomain g) = orbitSum G R d :=
  (orbitSum_eq_of_rel G ⟨g, hg, rfl⟩).symm

/-- Every orbit sum belongs to the `G`-invariant subalgebra. -/
theorem orbitSum_mem_permInvariantSubalgebra (G : Subgroup (Perm σ)) [Finite G] (d : σ →₀ ℕ) :
    orbitSum G R d ∈ permInvariantSubalgebra G R := by
  classical
  rw [mem_permInvariantSubalgebra_iff_coeff]
  intro g hg e
  have hiff : e.equivMapDomain g ∈ permOrbit G d ↔ e ∈ permOrbit G d :=
    ⟨fun h => (permOrbitRel G).trans h ⟨g⁻¹, G.inv_mem hg, by
      rw [← Finsupp.equivMapDomain_trans, Perm.inv_def, Equiv.self_trans_symm,
        Finsupp.equivMapDomain_refl]⟩,
     fun h => (permOrbitRel G).trans h ⟨g, hg, rfl⟩⟩
  simp [coeff_orbitSum, hiff]

/-- The orbit sum indexed by a `G`-orbit of exponent vectors. -/
noncomputable def orbitSumQuot (G : Subgroup (Perm σ)) [Finite G] (R : Type*) [CommSemiring R] :
    Quotient (permOrbitRel G) → MvPolynomial σ R :=
  Quotient.lift (orbitSum G R) fun _ _ h => orbitSum_eq_of_rel G h

@[simp]
theorem orbitSumQuot_mk (G : Subgroup (Perm σ)) [Finite G] (d : σ →₀ ℕ) :
    orbitSumQuot G R (Quotient.mk (permOrbitRel G) d) = orbitSum G R d := by
  rw [orbitSumQuot]; exact Quotient.lift_mk _ _ d

theorem orbitSumQuot_mem_permInvariantSubalgebra (G : Subgroup (Perm σ)) [Finite G]
    (q : Quotient (permOrbitRel G)) :
    orbitSumQuot G R q ∈ permInvariantSubalgebra G R :=
  Quotient.inductionOn q fun d => orbitSum_mem_permInvariantSubalgebra G d

theorem coeff_orbitSumQuot_of_eq (G : Subgroup (Perm σ)) [Finite G]
    {q : Quotient (permOrbitRel G)} {e : σ →₀ ℕ} (he : Quotient.mk (permOrbitRel G) e = q) :
    (orbitSumQuot G R q).coeff e = 1 := by
  subst he; exact coeff_orbitSum_self G e

theorem coeff_orbitSumQuot_of_ne (G : Subgroup (Perm σ)) [Finite G]
    {q : Quotient (permOrbitRel G)} {e : σ →₀ ℕ} (he : Quotient.mk (permOrbitRel G) e ≠ q) :
    (orbitSumQuot G R q).coeff e = 0 :=
  Quotient.inductionOn q (fun _ he =>
    coeff_orbitSum_of_notMem G (mt mem_permOrbit_iff_quotient_mk_eq.mp he)) he

/-- For a `G`-invariant polynomial `p`, its coefficient at `d` depends only on the `G`-orbit of
`d`. -/
private noncomputable def orbitCoeff (G : Subgroup (Perm σ)) (p : permInvariantSubalgebra G R) :
    Quotient (permOrbitRel G) → R :=
  Quotient.lift (fun d => (p : MvPolynomial σ R).coeff d) fun _ _ ⟨g, hg, hgd⟩ => by
    rw [← hgd, (mem_permInvariantSubalgebra_iff_coeff.mp p.2) g hg]

private theorem orbitCoeff_mk (G : Subgroup (Perm σ)) (p : permInvariantSubalgebra G R)
    (d : σ →₀ ℕ) :
    orbitCoeff G p (Quotient.mk (permOrbitRel G) d) = (p : MvPolynomial σ R).coeff d := by
  rw [orbitCoeff]; exact Quotient.lift_mk _ _ d

/-- The coefficient of `X^d` in a linear combination of orbit sums is the weight on the orbit of
`d`. -/
private theorem coeff_linearCombination_orbitSumQuot (G : Subgroup (Perm σ)) [Finite G]
    (c : Quotient (permOrbitRel G) →₀ R) (d : σ →₀ ℕ) :
    ((Finsupp.linearCombination R
        (fun q => (⟨orbitSumQuot G R q, orbitSumQuot_mem_permInvariantSubalgebra G q⟩ :
          permInvariantSubalgebra G R)) c : permInvariantSubalgebra G R) : MvPolynomial σ R).coeff d
      = c (Quotient.mk (permOrbitRel G) d) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum, ← Subalgebra.val_apply, map_sum, coeff_sum]
  have hterm : ∀ a, ((permInvariantSubalgebra G R).val (c a • (⟨orbitSumQuot G R a,
      orbitSumQuot_mem_permInvariantSubalgebra G a⟩ : permInvariantSubalgebra G R))).coeff d =
      if a = Quotient.mk (permOrbitRel G) d then c a else 0 := fun a => by
    rw [Subalgebra.val_apply, SetLike.val_smul, coeff_smul, smul_eq_mul]
    split_ifs with ha
    · rw [coeff_orbitSumQuot_of_eq G ha.symm, mul_one]
    · rw [coeff_orbitSumQuot_of_ne G (Ne.symm ha), mul_zero]
  simp_rw [hterm, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-- Coordinate projection of a `G`-invariant polynomial onto finitely supported functions on the
`G`-orbits of exponent vectors. -/
private noncomputable def orbitSumToFun (G : Subgroup (Perm σ)) (R : Type*)
    [CommSemiring R] :
    permInvariantSubalgebra G R →ₗ[R] (Quotient (permOrbitRel G) →₀ R) := by
  classical
  exact
    { toFun := fun p =>
        Finsupp.onFinset ((p : MvPolynomial σ R).support.image (Quotient.mk (permOrbitRel G)))
          (orbitCoeff G p) fun q hq => Quotient.inductionOn q (fun d hq =>
            Finset.mem_image_of_mem _ (mem_support_iff.mpr hq)) hq
      map_add' := fun _ _ => Finsupp.ext fun q =>
        Quotient.inductionOn q fun _ => by simp [orbitCoeff_mk]
      map_smul' := fun _ _ => Finsupp.ext fun q =>
        Quotient.inductionOn q fun _ => by simp [orbitCoeff_mk] }

private theorem orbitSumToFun_apply_mk (G : Subgroup (Perm σ))
    (p : permInvariantSubalgebra G R) (d : σ →₀ ℕ) :
    orbitSumToFun G R p (Quotient.mk (permOrbitRel G) d) = (p : MvPolynomial σ R).coeff d := by
  classical
  simp [orbitSumToFun, orbitCoeff_mk]

/-- The coordinate linear equivalence identifying `permInvariantSubalgebra G R` with finitely
supported `R`-valued functions on the `G`-orbits of exponent vectors. -/
private noncomputable def orbitSumRepr (G : Subgroup (Perm σ)) [Finite G] (R : Type*)
    [CommSemiring R] :
    permInvariantSubalgebra G R ≃ₗ[R] (Quotient (permOrbitRel G) →₀ R) :=
  LinearEquiv.ofLinearMap (orbitSumToFun G R)
    (Finsupp.linearCombination R fun q =>
      ⟨orbitSumQuot G R q, orbitSumQuot_mem_permInvariantSubalgebra G q⟩)
    (LinearMap.ext fun c => Finsupp.ext fun q => Quotient.inductionOn q fun d => by
      simpa [orbitSumToFun_apply_mk] using coeff_linearCombination_orbitSumQuot G c d)
    (LinearMap.ext fun p => Subtype.ext <| MvPolynomial.ext _ _ fun d => by
      simpa [orbitSumToFun_apply_mk] using
        coeff_linearCombination_orbitSumQuot G (orbitSumToFun G R p) d)

private theorem orbitSumRepr_symm_apply (G : Subgroup (Perm σ)) [Finite G]
    (c : Quotient (permOrbitRel G) →₀ R) :
    (orbitSumRepr G R).symm c = Finsupp.linearCombination R (fun q =>
      (⟨orbitSumQuot G R q, orbitSumQuot_mem_permInvariantSubalgebra G q⟩ :
        permInvariantSubalgebra G R)) c := by
  rw [orbitSumRepr, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap]

/-- **The orbit-sum basis** of the permutation-invariant subalgebra `permInvariantSubalgebra G R`:
for a finite permutation subgroup `G ≤ Equiv.Perm σ` and any commutative semiring `R`, the orbit
sums form a free `R`-module basis of `permInvariantSubalgebra G R`. -/
noncomputable def orbitSumBasis (G : Subgroup (Perm σ)) [Finite G] (R : Type*) [CommSemiring R] :
    Module.Basis (Quotient (permOrbitRel G)) R (permInvariantSubalgebra G R) :=
  Module.Basis.ofRepr (orbitSumRepr G R)

@[simp]
theorem coe_orbitSumBasis_apply (G : Subgroup (Perm σ)) [Finite G]
    (q : Quotient (permOrbitRel G)) :
    (orbitSumBasis G R q : MvPolynomial σ R) = orbitSumQuot G R q := by
  rw [orbitSumBasis, Module.Basis.coe_ofRepr]
  dsimp only
  rw [orbitSumRepr_symm_apply, Finsupp.linearCombination_single, one_smul]

@[simp]
theorem orbitSumBasis_repr_mk (G : Subgroup (Perm σ)) [Finite G]
    (p : permInvariantSubalgebra G R) (d : σ →₀ ℕ) :
    (orbitSumBasis G R).repr p (Quotient.mk (permOrbitRel G) d) =
      (p : MvPolynomial σ R).coeff d := by
  -- Unfold `(orbitSumBasis G R).repr` across the `Module.Basis.ofRepr` constructor.
  change orbitSumRepr G R p (Quotient.mk (permOrbitRel G) d) = _
  rw [orbitSumRepr, LinearEquiv.coe_ofLinearMap, orbitSumToFun_apply_mk]

end OrbitSum

end MvPolynomial

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

/-- The leading exponent of a nonzero `G`-invariant polynomial is `m`-maximal in its `G`-orbit. -/
theorem equivMapDomain_degree_le_of_mem_permInvariantSubalgebra [CommSemiring R]
    {G : Subgroup (Perm σ)} {p : MvPolynomial σ R}
    (hp : p ∈ permInvariantSubalgebra G R) (hp0 : p ≠ 0) {g : Perm σ} (hg : g ∈ G) :
    (m.degree p).equivMapDomain g ≼[m] m.degree p := by
  apply m.le_degree
  rw [mem_support_iff, (mem_permInvariantSubalgebra_iff_coeff.mp hp) g hg]
  exact m.leadingCoeff_ne_zero_iff.mpr hp0

/-- If `d` is `m`-maximal in its `G`-orbit, then `orbitSum G R d` has `m`-degree `d`. -/
theorem degree_orbitSum_of_forall_le [CommSemiring R] [Nontrivial R]
    {G : Subgroup (Perm σ)} [Finite G] {d : σ →₀ ℕ}
    (hd : ∀ g ∈ G, d.equivMapDomain g ≼[m] d) :
    m.degree (orbitSum G R d) = d := by
  apply m.toSyn.injective
  refine le_antisymm (m.degree_le_iff.2 fun e he => ?_) (m.le_degree <| by simp)
  rw [support_orbitSum, Set.Finite.mem_toFinset, mem_permOrbit_iff] at he
  obtain ⟨g, hg, rfl⟩ := he
  exact hd g hg

/-- If `d` is `m`-maximal in its `G`-orbit, then `orbitSum G R d` is monic
(leading coefficient `1`). -/
theorem leadingCoeff_orbitSum_of_forall_le [CommSemiring R] [Nontrivial R]
    {G : Subgroup (Perm σ)} [Finite G] {d : σ →₀ ℕ}
    (hd : ∀ g ∈ G, d.equivMapDomain g ≼[m] d) :
    m.leadingCoeff (orbitSum G R d) = 1 := by
  rw [leadingCoeff, m.degree_orbitSum_of_forall_le hd, coeff_orbitSum_self]

/-- **Leading exponents of a permutation-invariant subalgebra.** For a finite permutation subgroup
`G ≤ Equiv.Perm σ` and a monomial order `m`, an exponent `d` lies in
`m.leadingExponents (permInvariantSubalgebra G R)` if and only if `d` is `m`-maximal in its
`G`-orbit. -/
theorem mem_leadingExponents_permInvariantSubalgebra_iff
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {G : Subgroup (Perm σ)} [Finite G] {d : σ →₀ ℕ} :
    d ∈ m.leadingExponents (permInvariantSubalgebra G R) ↔
      ∀ g ∈ G, d.equivMapDomain g ≼[m] d := by
  rw [mem_leadingExponents_iff]
  exact ⟨fun ⟨_, hp, hp0, hd⟩ g hg => hd ▸ m.equivMapDomain_degree_le_of_mem_permInvariantSubalgebra
      hp hp0 hg,
    fun hd => ⟨orbitSum G R d, orbitSum_mem_permInvariantSubalgebra G d, orbitSum_ne_zero G d,
      m.degree_orbitSum_of_forall_le hd⟩⟩

end MonomialOrder
