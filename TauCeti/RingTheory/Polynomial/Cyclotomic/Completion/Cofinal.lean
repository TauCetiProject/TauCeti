/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Completion.Basic
public import TauCeti.RingTheory.Polynomial.FamilyLimit
import TauCeti.Algebra.Group.Pow
import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Cofinal presentations of the cyclotomic completion

Habiro's cyclotomic completion `CycloCompletion R S = lim_{f ∈ cycloIndex R S} R[q]/(f)` is the
polynomial-family limit along the members of the cyclotomic index monoid, so it can be computed
along any directed family of polynomials `h : κ → R[X]` that is mutually cofinal with
`cycloIndex R S`: every `h j` divides some cyclotomic index, and every cyclotomic index divides
some `h j`. This file identifies `CycloCompletion R S` with the polynomial-family limit
`TauCeti.PolyFamilyLimit h` of such a family, as topological `R`-algebras and compatibly with the
maps from `R[q]`, by the cofinal change of presentation `TauCeti.PolyFamilyLimit.cofinalEquiv`.
No hypothesis on `R` is needed.

For finite `S` the powers of `∏_{n ∈ S} Φ_n` form such a family, which presents
`CycloCompletion R S` as the inverse limit of the quotients `R[q]/((∏_{n ∈ S} Φ_n) ^ k)`; for
`S = {1}` these are the quotients `R[q]/((q - 1) ^ k)`.

## Main definitions

* `TauCeti.CycloCompletion.cofinalEquiv`: for a directed family `h` mutually cofinal with
  `cycloIndex R S`, the isomorphism `CycloCompletion R S ≃A[R] PolyFamilyLimit h`.
* `TauCeti.CycloCompletion.cycloProdPowEquiv`: for finite `S`, the isomorphism of
  `CycloCompletion R S` with the limit of the quotients by the powers of `cycloProd R hS`.

## Main results

* `TauCeti.CycloCompletion.proj_cofinalEquiv`, `TauCeti.CycloCompletion.proj_cofinalEquiv_symm`:
  the coordinate equations, reducing a dominating coordinate in either direction.
* `TauCeti.CycloCompletion.cofinalEquiv_fromPoly`,
  `TauCeti.CycloCompletion.cofinalEquiv_symm_fromPoly`: the comparison extends the identity of
  `R[q]`.
* `TauCeti.CycloCompletion.proj_cycloProdPowEquiv`,
  `TauCeti.CycloCompletion.proj_cycloProdPowEquiv_symm`: the coordinates of the finite
  presentation are the projections to the powers of `cycloProd R hS`.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §3.1, including (3.2).
-/

public section

open Polynomial

namespace TauCeti

namespace CycloCompletion

variable {R : Type*} [CommRing R] {S : Set ℕ} {κ : Type*}

/-! ### Mutually cofinal families -/

section Cofinal

variable {h : κ → R[X]} (hh : Directed (· ∣ ·) h) (hhS : ∀ j, ∃ f ∈ cycloIndex R S, h j ∣ f)
  (hSh : ∀ f ∈ cycloIndex R S, ∃ j, f ∣ h j)

/-- **Cyclotomic cofinal equivalence.** For a directed family of polynomials `h` that is mutually
cofinal with the cyclotomic index monoid `cycloIndex R S`, the cyclotomic completion is the limit
of the quotients `R[q]/(h j)`, as topological `R`-algebras, by the isomorphism induced by the
identity of `R[q]`. -/
noncomputable def cofinalEquiv : CycloCompletion R S ≃A[R] PolyFamilyLimit h :=
  PolyFamilyLimit.cofinalEquiv cycloIndex.directed_dvd hh
    (fun j ↦ (hhS j).elim fun f hf ↦ ⟨⟨f, hf.1⟩, hf.2⟩)
    (fun f ↦ hSh f f.property)

/-- The coordinate equation: the coordinate at `j` of the comparison reduces the projection to
any cyclotomic index `f` with `h j ∣ f`. -/
theorem proj_cofinalEquiv {j : κ} {f : cycloIndex R S} (hjf : h j ∣ f)
    (x : CycloCompletion R S) :
    PolyFamilyLimit.proj j (cofinalEquiv hh hhS hSh x) =
      AdjoinRoot.algHomOfDvd R (f : R[X]) (h j) hjf (PolyFamilyLimit.proj f x) :=
  PolyFamilyLimit.proj_cofinalEquiv _ _ _ _ hjf x

/-- The coordinate equation of the inverse: the projection to `f` reduces the coordinate at any
`j` with `f ∣ h j`. -/
theorem proj_cofinalEquiv_symm {f : cycloIndex R S} {j : κ} (hfj : (f : R[X]) ∣ h j)
    (y : PolyFamilyLimit h) :
    PolyFamilyLimit.proj f ((cofinalEquiv hh hhS hSh).symm y) =
      AdjoinRoot.algHomOfDvd R (h j) (f : R[X]) hfj (PolyFamilyLimit.proj j y) := by
  rw [cofinalEquiv, PolyFamilyLimit.cofinalEquiv_symm,
    PolyFamilyLimit.proj_cofinalEquiv _ _ _ _ hfj]

/-- The cyclotomic cofinal equivalence sends the image of a polynomial `p` in
`CycloCompletion R S` to its image in `PolyFamilyLimit h`. -/
@[simp]
theorem cofinalEquiv_fromPoly (p : R[X]) :
    cofinalEquiv hh hhS hSh (fromPoly R S p) = PolyFamilyLimit.fromPoly h p :=
  PolyFamilyLimit.cofinalEquiv_fromPoly _ _ _ _ p

/-- The inverse of the cyclotomic cofinal equivalence sends the image of a polynomial `p` in
`PolyFamilyLimit h` to its image in `CycloCompletion R S`. -/
@[simp]
theorem cofinalEquiv_symm_fromPoly (p : R[X]) :
    (cofinalEquiv hh hhS hSh).symm (PolyFamilyLimit.fromPoly h p) = fromPoly R S p := by
  rw [ContinuousAlgEquiv.symm_apply_eq, cofinalEquiv_fromPoly]

end Cofinal

/-! ### Finite sets of orders -/

section Finite

variable (hS : S.Finite)

/-- For finite `S`, `CycloCompletion R S` is the limit of the quotients of `R[q]` by the powers of
`∏_{n ∈ S} Φ_n`. -/
noncomputable def cycloProdPowEquiv :
    CycloCompletion R S ≃A[R] PolyFamilyLimit (fun k : ℕ ↦ cycloProd R hS ^ k) :=
  cofinalEquiv (directed_dvd_pow (cycloProd R hS))
    (fun k ↦ ⟨_, pow_mem (cycloProd_mem_cycloIndex R hS) k, dvd_refl _⟩)
    (fun _ hf ↦ exists_dvd_cycloProd_pow hS hf)

/-- The coordinate of `cycloProdPowEquiv` at `k` is the projection to `(cycloProd R hS) ^ k`. -/
@[simp]
theorem proj_cycloProdPowEquiv (k : ℕ) (x : CycloCompletion R S) :
    PolyFamilyLimit.proj k (cycloProdPowEquiv hS x) =
      PolyFamilyLimit.proj
        (⟨cycloProd R hS ^ k, pow_mem (cycloProd_mem_cycloIndex R hS) k⟩ : cycloIndex R S) x := by
  rw [cycloProdPowEquiv, proj_cofinalEquiv _ _ _ (j := k)
    (f := ⟨cycloProd R hS ^ k, pow_mem (cycloProd_mem_cycloIndex R hS) k⟩) (dvd_refl _),
    AdjoinRoot.algHomOfDvd_self, AlgHom.id_apply]

/-- The projection of `(cycloProdPowEquiv hS).symm y` to `(cycloProd R hS) ^ k` is the coordinate
of `y` at `k`. -/
@[simp]
theorem proj_cycloProdPowEquiv_symm (k : ℕ)
    (y : PolyFamilyLimit (fun k : ℕ ↦ cycloProd R hS ^ k)) :
    PolyFamilyLimit.proj
        (⟨cycloProd R hS ^ k, pow_mem (cycloProd_mem_cycloIndex R hS) k⟩ : cycloIndex R S)
        ((cycloProdPowEquiv hS).symm y) =
      PolyFamilyLimit.proj k y := by
  rw [← proj_cycloProdPowEquiv, ContinuousAlgEquiv.apply_symm_apply]

/-- The finite presentation sends the image of a polynomial `p` in `CycloCompletion R S` to its
image in the limit along the powers of `cycloProd R hS`. -/
@[simp]
theorem cycloProdPowEquiv_fromPoly (p : R[X]) :
    cycloProdPowEquiv hS (fromPoly R S p) =
      PolyFamilyLimit.fromPoly (fun k : ℕ ↦ cycloProd R hS ^ k) p :=
  cofinalEquiv_fromPoly _ _ _ p

/-- The inverse of the finite presentation sends the image of a polynomial `p` in the limit along
the powers of `cycloProd R hS` to its image in `CycloCompletion R S`. -/
@[simp]
theorem cycloProdPowEquiv_symm_fromPoly (p : R[X]) :
    (cycloProdPowEquiv hS).symm (PolyFamilyLimit.fromPoly (fun k : ℕ ↦ cycloProd R hS ^ k) p) =
      fromPoly R S p :=
  cofinalEquiv_symm_fromPoly _ _ _ p

end Finite

end CycloCompletion

/-! ### Examples -/

/-- Powers of `q - 1` are not cofinal in the integral cyclotomic system of all positive orders:
no power of `q - 1` is divisible by `Φ₂ = q + 1`. -/
example (k : ℕ) : ¬ cyclotomic 2 ℤ ∣ (X - 1 : ℤ[X]) ^ k := by
  intro h
  have := eval_dvd (x := -1) h
  simp only [cyclotomic_two, eval_add, eval_X, eval_one, neg_add_cancel, eval_pow, eval_sub,
    zero_dvd_iff, pow_eq_zero_iff', ne_eq] at this
  omega

end TauCeti
