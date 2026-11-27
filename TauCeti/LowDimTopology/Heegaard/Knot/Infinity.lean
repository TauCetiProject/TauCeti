/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.MvPolynomial.Fin.Two
public import TauCeti.LowDimTopology.Heegaard.Knot.Differential
public import TauCeti.RingTheory.MvPolynomial.Basic

/-!
# The doubly filtered infinity knot complex and `CFK^∞`

Let `(Σ, α, β, w, z)` be a doubly pointed Heegaard diagram and `A` an Alexander grading of its
generators. In the notation of Ozsváth and Szabó, the knot Floer complex `CFK^∞` is the
`𝔽₂`-vector space with basis the triples `[x, i, j]` of a generator `x` and integers `i` and `j`
with `j - i = A(x)`, with differential

`∂ [x, i, j] = ∑_y ∑_φ [y, i - n_w(φ), j - n_z(φ)]`,

the sum over the Whitney disks `φ` of Maslov index one from `x` to `y`. This file builds the same
differential on the **full infinity knot complex**, with basis all triples `[x, i, j]`, and cuts
`CFK^∞` out of it by the condition `j - i = A(x)`. The full complex is the knot complex of Zemke
over `𝔽₂[U, U⁻¹, V, V⁻¹]`, the triple `[x, i, j]` being the chain `U ^ (-i) V ^ (-j) x`; it is the
direct sum of one copy of `CFK^∞` for each value of `j - i - A(x)`. The differential is built from
the knot coefficients `TauCeti.HeegaardRegionSystem.knotCoefficient`, which count nonnegative
domains in place of holomorphic disks.

* The **cells** are the triples `[x, i, j]`, elements of `H.Generator × ℤ × ℤ`, and the chains of
  the full infinity knot complex are the finitely supported functions
  `H.Generator × ℤ × ℤ →₀ ZMod 2`.
* Placing the chain `U ^ a V ^ b x` of the full knot complex over `𝔽₂[U, V]` at the cell
  `[x, i - a, j - b]` defines, for every pair `(i, j)`, an injective linear map
  `TauCeti.HeegaardRegionSystem.knotInfinityLift` from the free `𝔽₂[U, V]`-module on the
  generators to the chains (`knotInfinityLift_injective`).
* The **infinity knot differential** `H.knotInfinityDifferential χ w z` sends `[x, i, j]` to the
  image under this map of the knot differential of `x`. It is intertwined with the knot
  differential (`knotInfinityDifferential_knotInfinityLift`), so it squares to zero exactly when
  the knot differential does (`knotInfinityDifferential_comp_self_eq_zero_iff`).
* The shifts `[x, i, j] ↦ [x, i - a, j - b]` (`TauCeti.HeegaardRegionSystem.knotInfinityShift`)
  form an action of `ℤ × ℤ` (`knotInfinityShift_zero`, `knotInfinityShift_add`) and commute with
  the differential (`knotInfinityDifferential_knotInfinityShift`). The shifts by `(1, 0)` and
  `(0, 1)` are the actions of the two variables `U` and `V` of Zemke's complex. The shifts by
  `(a, a)` preserve `CFK^∞` (`knotInfinityShift_mem_knotInfinityAlexanderSubmodule_iff`), and the
  shift by `(1, 1)` is the action of `U` on `CFK^∞` of Ozsváth and Szabó.

**Filtrations.** The terms of the differential have `n_w(φ), n_z(φ) ≥ 0`, so the differential
does not increase either index. For every lower set `S` of `ℤ × ℤ`, the chains of the full complex
supported on the cells `[x, i, j]` with `(i, j) ∈ S`
(`TauCeti.HeegaardRegionSystem.knotInfinityFiltration`) form a subcomplex
(`knotInfinityFiltration_le_comap_knotInfinityDifferential`), and the differential descends to the
quotient (`TauCeti.HeegaardRegionSystem.knotInfinityQuotientDifferential`). The shift by `(a, b)`
moves the filtration by `(a, b)` (`knotInfinityShift_mem_knotInfinityFiltration_iff`). Intersected
with `CFK^∞`, the set `S = {(i, j) | i < 0}` gives the subcomplex `C{i < 0}` and the quotient
`C{i ≥ 0}` of Ozsváth and Szabó, from which the minus and plus flavors are cut out; that
intersection is not formed here.

**The Alexander grading and the ambient complex.** For an Alexander grading `A` of the generators,
`A(x) - A(y) = n_z(D) - n_w(D)` for every domain `D` from `x` to `y`
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.alexander_sub_alexander`), the chains supported on
the cells with `j - i = A(x)` (`TauCeti.HeegaardRegionSystem.knotInfinityAlexanderSubmodule`) form a
subcomplex (`knotInfinityAlexanderSubmodule_le_comap_knotInfinityDifferential`): this is the
complex `CFK^∞` of Ozsváth and Szabó. Forgetting `j`, the map
`[x, i, j] ↦ U ^ (-i) x` (`TauCeti.HeegaardRegionSystem.knotInfinityForget`) to the chains of
`CF^∞` of the diagram pointed at `w` alone intertwines the infinity knot differential with the
infinity differential `TauCeti.HeegaardRegionSystem.infinityDifferential` of that diagram
(`knotInfinityForget_knotInfinityDifferential`) and the shift by `(a, b)` with multiplication by
`U ^ a` (`knotInfinityForget_knotInfinityShift`), and on `CFK^∞` it is a linear isomorphism
(`TauCeti.HeegaardRegionSystem.knotInfinityAlexanderEquiv`). So `CFK^∞` is `CF^∞` of the ambient
manifold, as a module over `𝔽₂[U, U⁻¹]`, with the second filtration by `j` recording the
multiplicities at `z`.

As for the knot differential, these are counts of domains rather than of holomorphic disks, and
`∂ ∘ ∂ = 0` is not proved here; it is equivalent to the same statement for the knot differential.

## Main definitions

* `TauCeti.HeegaardRegionSystem.knotInfinityLift`: the chain `U ^ a V ^ b x` placed at
  `[x, i - a, j - b]`.
* `TauCeti.HeegaardRegionSystem.knotInfinityDifferential`: the differential of the full infinity
  knot complex; its restriction to the Alexander subcomplex is the differential of `CFK^∞`.
* `TauCeti.HeegaardRegionSystem.knotInfinityShift`: the shifts of both indices.
* `TauCeti.HeegaardRegionSystem.knotInfinityFiltration`: the chains over a set of filtration
  levels, and `TauCeti.HeegaardRegionSystem.knotInfinityQuotientDifferential` the differential of
  the quotient by a lower set.
* `TauCeti.HeegaardRegionSystem.knotInfinityAlexanderSubmodule`: the chains with `j - i = A(x)`,
  those of `CFK^∞`.
* `TauCeti.HeegaardRegionSystem.knotInfinityForget`: forgetting the index `j`.
* `TauCeti.HeegaardRegionSystem.knotInfinityAlexanderEquiv`: `CFK^∞` is linearly isomorphic to
  `CF^∞` of the ambient manifold.

## Main results

* `TauCeti.HeegaardRegionSystem.knotInfinityDifferential_knotInfinityLift` and
  `TauCeti.HeegaardRegionSystem.knotInfinityDifferential_comp_self_eq_zero_iff`: comparison with
  the knot differential over `𝔽₂[U, V]`.
* `TauCeti.HeegaardRegionSystem.knotInfinityDifferential_knotInfinityShift`: the differential
  commutes with the shifts.
* `TauCeti.HeegaardRegionSystem.knotInfinityFiltration_le_comap_knotInfinityDifferential`: the
  differential preserves the double filtration.
* `HeegaardRegionSystem.knotInfinityAlexanderSubmodule_le_comap_knotInfinityDifferential`: the
  Alexander grading cuts out a subcomplex.
* `TauCeti.HeegaardRegionSystem.knotInfinityForget_knotInfinityDifferential` and
  `HeegaardRegionSystem.knotInfinityAlexanderEquiv_restrict_knotInfinityDifferential`: forgetting
  `j` is a chain map, and an isomorphism of complexes from `CFK^∞` onto `CF^∞` of the diagram
  pointed at `w`.
* `TauCeti.HeegaardRegionSystem.knotInfinityAlexanderEquiv_knotInfinityShift`: this isomorphism
  turns the action of `U` on `CFK^∞` into multiplication by `U` on `CF^∞`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), §3 (the complex `CFK^∞`, its
  differential, its `ℤ ⊕ ℤ` filtration and the action of `U`).
* I. Zemke, *Link cobordisms and functoriality in link Floer homology*, J. Topol. **12** (2019),
  [arXiv:1610.05207](https://arxiv.org/abs/1610.05207) (the knot complex over `𝔽₂[U, V]`).
-/

public section

open MvPolynomial LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section Lift

variable (H) in
/-- The chains of the full knot complex over `𝔽₂[U, V]` placed at the level `(i, j)`: the
`𝔽₂`-linear map sending `U ^ a V ^ b x`, with `U = X 0` and `V = X 1`, to the cell
`[x, i - a, j - b]`. -/
noncomputable def knotInfinityLift (i j : ℤ) :
    (H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)) →ₗ[ZMod 2] H.Generator × ℤ × ℤ →₀ ZMod 2 :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2)
      (fun s : (_ : H.Generator) × (Fin 2 →₀ ℕ) => (s.1, i - s.2 0, j - s.2 1)) ∘ₗ
    (Finsupp.basis fun _ => basisMonomials (Fin 2) (ZMod 2)).repr.toLinearMap

variable {i j : ℤ}

/-- The monomial `a U ^ m 0 V ^ m 1 x` placed at the level `(i, j)` is `a [x, i - m 0, j - m 1]`. -/
@[simp]
theorem knotInfinityLift_single_monomial (x : H.Generator) (m : Fin 2 →₀ ℕ) (a : ZMod 2) :
    H.knotInfinityLift i j (Finsupp.single x (monomial m a)) =
      Finsupp.single (x, i - m 0, j - m 1) a := by
  have h : Finsupp.single x (monomial m a) =
      a • (Finsupp.basis fun _ : H.Generator => basisMonomials (Fin 2) (ZMod 2)) ⟨x, m⟩ := by
    simp [Finsupp.smul_single, smul_monomial]
  rw [h, map_smul]
  simp only [knotInfinityLift, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- A cell in the support of a lifted chain `c` is `[y, i - m 0, j - m 1]` for a monomial
`U ^ m 0 V ^ m 1` with nonzero coefficient in `c y`. -/
theorem exists_coeff_ne_zero_of_mem_support_knotInfinityLift
    {c : H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)} {g : H.Generator × ℤ × ℤ}
    (hg : g ∈ (H.knotInfinityLift i j c).support) :
    ∃ m : Fin 2 →₀ ℕ, (c g.1).coeff m ≠ 0 ∧ g = (g.1, i - m 0, j - m 1) := by
  classical
  obtain ⟨⟨y, m⟩, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
  have hrepr := (Finsupp.basis_repr (fun _ => basisMonomials (Fin 2) (ZMod 2)) c ⟨y, m⟩).trans
    (basisMonomials_repr_apply (c y) m)
  exact ⟨m, hrepr.symm.trans_ne (Finsupp.mem_support_iff.mp hs), rfl⟩

/-- Placing chains at a level is injective. -/
theorem knotInfinityLift_injective : Function.Injective (H.knotInfinityLift i j) := by
  refine (Finsupp.mapDomain_injective ?_).comp (LinearEquiv.injective _)
  rintro ⟨x, m⟩ ⟨y, m'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h0, h1⟩ := h
  obtain rfl : m = m' := by
    ext k
    fin_cases k <;> simp <;> omega
  rfl

/-- Multiplying by the monomial `U ^ m 0 V ^ m 1` and placing at the level `(i, j)` is placing at
the level `(i - m 0, j - m 1)`. -/
theorem knotInfinityLift_monomial_smul (m : Fin 2 →₀ ℕ)
    (c : H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)) :
    H.knotInfinityLift i j (monomial m (1 : ZMod 2) • c) =
      H.knotInfinityLift (i - m 0) (j - m 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [smul_add, map_add, map_add, hc, hd]
  | single y p =>
    induction p using MvPolynomial.induction_on' with
    | monomial m' a =>
      rw [Finsupp.smul_single, smul_eq_mul, monomial_mul_monomial, one_mul,
        knotInfinityLift_single_monomial, knotInfinityLift_single_monomial]
      simp [sub_add_eq_sub_sub]
    | add p q hp hq => rw [Finsupp.single_add, smul_add, map_add, map_add, hp, hq]

/-- Every lifted chain is supported on cells below the level `(i, j)`. -/
theorem knotInfinityLift_mem_supported (c : H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)) :
    H.knotInfinityLift i j c ∈
      Finsupp.supported (ZMod 2) (ZMod 2) {g : H.Generator × ℤ × ℤ | g.2 ≤ (i, j)} := by
  intro g hg
  obtain ⟨m, -, hgm⟩ := exists_coeff_ne_zero_of_mem_support_knotInfinityLift hg
  rw [Set.mem_ofPred_eq, hgm, Prod.mk_le_mk]
  omega

end Lift

section Differential

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

variable (H) in
/-- The infinity knot differential of a doubly pointed Heegaard diagram, with region
Euler characteristics `χ` and basepoints `w` and `z`: the `𝔽₂`-linear endomorphism of the chains
on the cells `[x, i, j]` sending `[x, i, j]` to the sum of `[y, i - n_w(D), j - n_z(D)]` over the
nonnegative domains `D` of Maslov index one from `x` to `y`, that is, to the knot differential of
`x` placed at the level `(i, j)`. This is the differential of the full infinity knot complex; its
restriction to `TauCeti.HeegaardRegionSystem.knotInfinityAlexanderSubmodule` for an Alexander
grading is the differential of `CFK^∞`. -/
noncomputable def knotInfinityDifferential (χ : Region → ℤ) (w z : Basepoint) :
    (H.Generator × ℤ × ℤ →₀ ZMod 2) →ₗ[ZMod 2] H.Generator × ℤ × ℤ →₀ ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) fun g =>
    H.knotInfinityLift g.2.1 g.2.2 (H.knotDifferential χ w z (Finsupp.single g.1 1))

variable {χ : Region → ℤ} {w z : Basepoint}

/-- The infinity knot differential of a cell `[x, i, j]` is the knot differential of `x` placed at
the level `(i, j)`. -/
@[simp]
theorem knotInfinityDifferential_single (x : H.Generator) (i j : ℤ) (a : ZMod 2) :
    H.knotInfinityDifferential χ w z (Finsupp.single (x, i, j) a) =
      a • H.knotInfinityLift i j (H.knotDifferential χ w z (Finsupp.single x 1)) :=
  Finsupp.linearCombination_single _ _ _

/-- **The infinity knot differential extends the knot differential.** Placing the chains of the
knot complex over `𝔽₂[U, V]` at any level intertwines the knot differential with the infinity knot
differential. -/
@[simp]
theorem knotInfinityDifferential_knotInfinityLift (i j : ℤ)
    (c : H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)) :
    H.knotInfinityDifferential χ w z (H.knotInfinityLift i j c) =
      H.knotInfinityLift i j (H.knotDifferential χ w z c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single x p =>
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
      have h : Finsupp.single x (monomial m a) =
          a • monomial m (1 : ZMod 2) • Finsupp.single x (1 : MvPolynomial (Fin 2) (ZMod 2)) := by
        simp [Finsupp.smul_single, smul_monomial]
      rw [knotInfinityLift_single_monomial, knotInfinityDifferential_single, h,
        LinearMap.map_smul_of_tower, map_smul, map_smul, knotInfinityLift_monomial_smul]
    | add p q hp hq => rw [Finsupp.single_add, map_add, map_add, hp, hq, map_add, map_add]

/-- **Reduction of `∂ ∘ ∂ = 0` to the knot differential.** The infinity knot differential squares
to zero exactly when the knot differential over `𝔽₂[U, V]` does. -/
theorem knotInfinityDifferential_comp_self_eq_zero_iff :
    H.knotInfinityDifferential χ w z ∘ₗ H.knotInfinityDifferential χ w z = 0 ↔
      H.knotDifferential χ w z ∘ₗ H.knotDifferential χ w z = 0 := by
  constructor
  · intro h
    refine LinearMap.ext fun c => ?_
    apply knotInfinityLift_injective (H := H) (i := 0) (j := 0)
    rw [LinearMap.comp_apply, ← knotInfinityDifferential_knotInfinityLift,
      ← knotInfinityDifferential_knotInfinityLift, ← LinearMap.comp_apply, h]
    simp
  · intro h
    refine Finsupp.lhom_ext fun g a => ?_
    rw [LinearMap.comp_apply, knotInfinityDifferential_single, map_smul,
      knotInfinityDifferential_knotInfinityLift, ← LinearMap.comp_apply, h]
    simp

end Differential

section Shift

variable (H) in
/-- The shift of both indices of the cells by `(a, b)`, `[x, i, j] ↦ [x, i - a, j - b]`. The shift
by `(1, 1)` is the action of `U` on `CFK^∞` of Ozsváth and Szabó. -/
noncomputable def knotInfinityShift (a b : ℤ) :
    (H.Generator × ℤ × ℤ →₀ ZMod 2) ≃ₗ[ZMod 2] H.Generator × ℤ × ℤ →₀ ZMod 2 :=
  Finsupp.domLCongr ((Equiv.refl H.Generator).prodCongr
    ((Equiv.subRight a).prodCongr (Equiv.subRight b)))

/-- The shift by `(a, b)` sends `[x, i, j]` to `[x, i - a, j - b]`. -/
@[simp]
theorem knotInfinityShift_single (a b : ℤ) (x : H.Generator) (i j : ℤ) (c : ZMod 2) :
    H.knotInfinityShift a b (Finsupp.single (x, i, j) c) = Finsupp.single (x, i - a, j - b) c :=
  Finsupp.domLCongr_single _ _ _

/-- The shift by `(0, 0)` is the identity. -/
@[simp]
theorem knotInfinityShift_zero : H.knotInfinityShift 0 0 = LinearEquiv.refl (ZMod 2) _ :=
  LinearEquiv.toLinearMap_injective <| Finsupp.lhom_ext fun ⟨x, i, j⟩ c => by simp

/-- Shifting by `(a, b)` and then by `(a', b')` is shifting by `(a + a', b + b')`. -/
theorem knotInfinityShift_add (a b a' b' : ℤ) :
    H.knotInfinityShift (a + a') (b + b') =
      (H.knotInfinityShift a b).trans (H.knotInfinityShift a' b') :=
  LinearEquiv.toLinearMap_injective <| Finsupp.lhom_ext fun ⟨x, i, j⟩ c => by
    simp [sub_add_eq_sub_sub]

/-- The inverse of the shift by `(a, b)` is the shift by `(-a, -b)`. -/
@[simp]
theorem knotInfinityShift_symm (a b : ℤ) :
    (H.knotInfinityShift a b).symm = H.knotInfinityShift (-a) (-b) :=
  LinearEquiv.toLinearMap_injective <| Finsupp.lhom_ext fun ⟨x, i, j⟩ c => by
    simp [LinearEquiv.symm_apply_eq]

/-- Shifting a chain placed at the level `(i, j)` by `(a, b)` places it at the level
`(i - a, j - b)`. -/
@[simp]
theorem knotInfinityShift_knotInfinityLift (a b i j : ℤ)
    (c : H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)) :
    H.knotInfinityShift a b (H.knotInfinityLift i j c) = H.knotInfinityLift (i - a) (j - b) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add]
  | single y p =>
    induction p using MvPolynomial.induction_on' with
    | monomial m e =>
      rw [knotInfinityLift_single_monomial, knotInfinityLift_single_monomial,
        knotInfinityShift_single]
      congr 1
      exact Prod.ext rfl (Prod.ext (by ring) (by ring))
    | add p q hp hq => rw [Finsupp.single_add, map_add, map_add, hp, hq, map_add]

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

variable {χ : Region → ℤ} {w z : Basepoint}

/-- **The infinity knot differential commutes with the shifts**, in particular with the action of
`U`. -/
theorem knotInfinityDifferential_knotInfinityShift (a b : ℤ) (c : H.Generator × ℤ × ℤ →₀ ZMod 2) :
    H.knotInfinityDifferential χ w z (H.knotInfinityShift a b c) =
      H.knotInfinityShift a b (H.knotInfinityDifferential χ w z c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single g e =>
    obtain ⟨x, i, j⟩ := g
    rw [knotInfinityShift_single, knotInfinityDifferential_single,
      knotInfinityDifferential_single, map_smul, knotInfinityShift_knotInfinityLift]

end Shift

section Filtration

variable (H) in
/-- The chains of the full infinity knot complex supported on the cells `[x, i, j]` whose filtration
level `(i, j)` lies in the set `S`. -/
def knotInfinityFiltration (S : Set (ℤ × ℤ)) :
    Submodule (ZMod 2) (H.Generator × ℤ × ℤ →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) (Prod.snd ⁻¹' S)

/-- A chain lies in the filtration piece over `S` exactly when every cell `[x, i, j]` of its
support has `(i, j) ∈ S`. -/
theorem mem_knotInfinityFiltration_iff {S : Set (ℤ × ℤ)} {c : H.Generator × ℤ × ℤ →₀ ZMod 2} :
    c ∈ H.knotInfinityFiltration S ↔ ∀ g ∈ c.support, g.2 ∈ S :=
  Iff.rfl

/-- The shift by `(a, b)` moves the filtration by `(a, b)`: a shifted chain lies over the levels
`p` with `p + (a, b) ∈ S` exactly when the chain lies over `S`. -/
theorem knotInfinityShift_mem_knotInfinityFiltration_iff {a b : ℤ} {S : Set (ℤ × ℤ)}
    {c : H.Generator × ℤ × ℤ →₀ ZMod 2} :
    H.knotInfinityShift a b c ∈ H.knotInfinityFiltration ((· + (a, b)) ⁻¹' S) ↔
      c ∈ H.knotInfinityFiltration S := by
  simp only [mem_knotInfinityFiltration_iff, knotInfinityShift, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, ne_eq,
    Set.mem_preimage, Prod.forall, Prod.map_apply, id_eq, Equiv.subRight_symm_apply, Prod.mk_add_mk]
  refine ⟨fun h x i j hc => ?_, fun h x i j hc => h x _ _ hc⟩
  simpa using h x (i - a) (j - b) (by simpa using hc)

/-- For a lower set `S` and `a, b ≥ 0`, the shift by `(a, b)` preserves the chains over `S`. In
particular the actions of `U` and `V` preserve the double filtration. -/
theorem knotInfinityShift_mem_knotInfinityFiltration {a b : ℤ} {S : Set (ℤ × ℤ)}
    (hS : IsLowerSet S) (ha : 0 ≤ a) (hb : 0 ≤ b) {c : H.Generator × ℤ × ℤ →₀ ZMod 2}
    (hc : c ∈ H.knotInfinityFiltration S) :
    H.knotInfinityShift a b c ∈ H.knotInfinityFiltration S := by
  have h := (knotInfinityShift_mem_knotInfinityFiltration_iff (a := a) (b := b)).mpr hc
  rw [mem_knotInfinityFiltration_iff] at h ⊢
  exact fun g hg => hS (by simp [Prod.le_def, ha, hb]) (h g hg)

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

variable {χ : Region → ℤ} {w z : Basepoint}

/-- **The infinity knot differential preserves the double filtration.** For a lower set `S` of
`ℤ × ℤ`, the chains over `S` form a subcomplex. -/
theorem knotInfinityFiltration_le_comap_knotInfinityDifferential {S : Set (ℤ × ℤ)}
    (hS : IsLowerSet S) :
    H.knotInfinityFiltration S ≤
      (H.knotInfinityFiltration S).comap (H.knotInfinityDifferential χ w z) := by
  intro c hc
  rw [Submodule.mem_comap, knotInfinityDifferential, Finsupp.linearCombination_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun g hg => Submodule.smul_mem _ _ ?_
  refine Finsupp.supported_mono (fun g' hg' => ?_) (knotInfinityLift_mem_supported _)
  exact hS hg' (hc (Finsupp.mem_support_iff.mpr hg))

variable (H) in
/-- The differential of the quotient of the full infinity knot complex by the subcomplex over a
lower set `S` of filtration levels, induced by the infinity knot differential. For
`S = {(i, j) | i < 0}`, intersecting with `CFK^∞` would give the complex `C{i ≥ 0}` of Ozsváth and
Szabó; that intersection is not formed here. -/
noncomputable def knotInfinityQuotientDifferential (χ : Region → ℤ) (w z : Basepoint)
    {S : Set (ℤ × ℤ)} (hS : IsLowerSet S) :
    ((H.Generator × ℤ × ℤ →₀ ZMod 2) ⧸ H.knotInfinityFiltration S) →ₗ[ZMod 2]
      (H.Generator × ℤ × ℤ →₀ ZMod 2) ⧸ H.knotInfinityFiltration S :=
  (H.knotInfinityFiltration S).mapQ (H.knotInfinityFiltration S) (H.knotInfinityDifferential χ w z)
    (knotInfinityFiltration_le_comap_knotInfinityDifferential hS)

/-- The quotient differential of the class of a chain is the class of its infinity knot
differential. -/
@[simp]
theorem knotInfinityQuotientDifferential_mk {S : Set (ℤ × ℤ)} (hS : IsLowerSet S)
    (c : H.Generator × ℤ × ℤ →₀ ZMod 2) :
    H.knotInfinityQuotientDifferential χ w z hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (H.knotInfinityDifferential χ w z c) :=
  Submodule.mapQ_apply _ _ _ c

end Filtration

section Alexander

variable (H) in
/-- The chains of the knot complex `CFK^∞` of Ozsváth and Szabó for an Alexander grading `A` of the
generators: those supported on the cells `[x, i, j]` with `j - i = A(x)`. -/
def knotInfinityAlexanderSubmodule (A : H.Generator → ℤ) :
    Submodule (ZMod 2) (H.Generator × ℤ × ℤ →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) {g | g.2.2 - g.2.1 = A g.1}

/-- A chain lies in `CFK^∞` for the Alexander grading `A` exactly when every cell `[x, i, j]` of
its support has `j - i = A(x)`. -/
theorem mem_knotInfinityAlexanderSubmodule_iff {A : H.Generator → ℤ}
    {c : H.Generator × ℤ × ℤ →₀ ZMod 2} :
    c ∈ H.knotInfinityAlexanderSubmodule A ↔ ∀ g ∈ c.support, g.2.2 - g.2.1 = A g.1 :=
  Iff.rfl

/-- The shifts by `(a, a)`, in particular the action of `U` of Ozsváth and Szabó, preserve
`CFK^∞`. -/
theorem knotInfinityShift_mem_knotInfinityAlexanderSubmodule_iff {a : ℤ} {A : H.Generator → ℤ}
    {c : H.Generator × ℤ × ℤ →₀ ZMod 2} :
    H.knotInfinityShift a a c ∈ H.knotInfinityAlexanderSubmodule A ↔
      c ∈ H.knotInfinityAlexanderSubmodule A := by
  simp only [mem_knotInfinityAlexanderSubmodule_iff, knotInfinityShift, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, ne_eq,
    Prod.forall, Prod.map_apply, id_eq, Equiv.subRight_symm_apply]
  refine ⟨fun h x i j hc => ?_, fun h x i j hc => by simpa using h x _ _ hc⟩
  simpa using h x (i - a) (j - a) (by simpa using hc)

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

variable {χ : Region → ℤ} {w z : Basepoint} {A : H.Generator → ℤ}

/-- **The Alexander grading cuts out a subcomplex.** For an Alexander grading `A` of the
generators, with `A(x) - A(y) = n_z(D) - n_w(D)` for every domain `D` from `x` to `y`, the infinity
knot differential preserves the chains on the cells with `j - i = A(x)`. -/
theorem knotInfinityAlexanderSubmodule_le_comap_knotInfinityDifferential
    (hA : ∀ {x y : H.Generator} {D : Region → ℤ}, H.IsDomainBetween x y D →
      A x - A y = D (H.basepoint z) - D (H.basepoint w)) :
    H.knotInfinityAlexanderSubmodule A ≤
      (H.knotInfinityAlexanderSubmodule A).comap (H.knotInfinityDifferential χ w z) := by
  intro c hc
  rw [Submodule.mem_comap, knotInfinityDifferential, Finsupp.linearCombination_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun g hg => Submodule.smul_mem _ _ fun g' hg' => ?_
  obtain ⟨m, hm, hg'm⟩ := exists_coeff_ne_zero_of_mem_support_knotInfinityLift hg'
  rw [knotDifferential_single_apply, one_mul] at hm
  have h := sub_eq_of_coeff_knotCoefficient_ne_zero hA hm
  have hg := hc (Finsupp.mem_support_iff.mpr hg)
  simp only [Set.mem_ofPred_eq] at hg ⊢
  rw [hg'm]
  dsimp only
  omega

end Alexander

section Forget

variable (H) in
/-- Forgetting the second index: the `𝔽₂`-linear map sending the cell `[x, i, j]` to the chain
`U ^ (-i) x` of `CF^∞`, with Laurent coefficients in `U = T 1`. -/
noncomputable def knotInfinityForget :
    (H.Generator × ℤ × ℤ →₀ ZMod 2) →ₗ[ZMod 2] H.Generator →₀ (ZMod 2)[T;T⁻¹] :=
  Finsupp.linearCombination (ZMod 2) fun g => Finsupp.single g.1 (T (-g.2.1))

/-- Forgetting the second index sends `a [x, i, j]` to `a U ^ (-i) x`. -/
@[simp]
theorem knotInfinityForget_single (x : H.Generator) (i j : ℤ) (a : ZMod 2) :
    H.knotInfinityForget (Finsupp.single (x, i, j) a) = a • Finsupp.single x (T (-i)) :=
  Finsupp.linearCombination_single _ _ _

/-- Forgetting the second index of a chain placed at the level `(i, j)` multiplies by `U ^ (-i)`
the chain obtained by setting `V = 1`. -/
theorem knotInfinityForget_knotInfinityLift (i j : ℤ)
    (c : H.Generator →₀ MvPolynomial (Fin 2) (ZMod 2)) :
    H.knotInfinityForget (H.knotInfinityLift i j c) =
      (T (-i) : (ZMod 2)[T;T⁻¹]) • Finsupp.mapRange (fun p => Polynomial.toLaurent (R := ZMod 2)
        (aeval ![(Polynomial.X : Polynomial (ZMod 2)), 1] p)) (by simp) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapRange_add (by simp), smul_add]
  | single x p =>
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
      simp only [knotInfinityLift_single_monomial, knotInfinityForget_single,
        Finsupp.mapRange_single, Finsupp.smul_single, aeval_monomial_fin_two]
      congr 1
      simp [LaurentPolynomial.smul_eq_C_mul, sub_eq_add_neg]
    | add p q hp hq =>
      rw [Finsupp.single_add, map_add, map_add, hp, hq, ← smul_add,
        ← Finsupp.mapRange_add (by simp)]

/-- Forgetting the second index turns the shift by `(a, b)` into multiplication by `U ^ a`. -/
theorem knotInfinityForget_knotInfinityShift (a b : ℤ) (c : H.Generator × ℤ × ℤ →₀ ZMod 2) :
    H.knotInfinityForget (H.knotInfinityShift a b c) =
      (T a : (ZMod 2)[T;T⁻¹]) • H.knotInfinityForget c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, smul_add]
  | single g e =>
    obtain ⟨x, i, j⟩ := g
    rw [knotInfinityShift_single, knotInfinityForget_single, knotInfinityForget_single, smul_comm]
    congr 1
    rw [Finsupp.smul_single, smul_eq_mul, ← T_add, neg_sub, sub_eq_add_neg]

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

variable {χ : Region → ℤ} {w z : Basepoint}

/-- **Forgetting the second index is a chain map** from `CFK^∞` to `CF^∞` of the diagram pointed
at `w` alone: it intertwines the infinity knot differential with the infinity differential of
that diagram. -/
theorem knotInfinityForget_knotInfinityDifferential (c : H.Generator × ℤ × ℤ →₀ ZMod 2) :
    H.knotInfinityForget (H.knotInfinityDifferential χ w z c) =
      (H.withBasepoints fun _ : Unit => H.basepoint w).infinityDifferential χ
        (H.knotInfinityForget c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single g a =>
    obtain ⟨x, i, j⟩ := g
    rw [knotInfinityDifferential_single, map_smul, knotInfinityForget_knotInfinityLift,
      knotInfinityForget_single, LinearMap.map_smul_of_tower]
    congr 1
    ext y
    rw [Finsupp.smul_apply, Finsupp.mapRange_apply, knotDifferential_single_apply, one_mul,
      aeval_knotCoefficient_X_one, infinityDifferential_single_apply, smul_eq_mul]

end Forget

section AlexanderEquiv

variable (H) in
/-- The inverse of forgetting the second index on `CFK^∞` for an Alexander grading `A`: the
`𝔽₂`-linear map sending the chain `U ^ k x` of `CF^∞` to the cell `[x, -k, A(x) - k]`. -/
noncomputable def knotInfinityAlexanderLift (A : H.Generator → ℤ) :
    (H.Generator →₀ (ZMod 2)[T;T⁻¹]) →ₗ[ZMod 2] H.Generator × ℤ × ℤ →₀ ZMod 2 :=
  Finsupp.lsum (ZMod 2) fun x => Finsupp.lmapDomain (ZMod 2) (ZMod 2)
    (fun k : ℤ => (x, -k, A x - k)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap

variable {A : H.Generator → ℤ}

/-- The inverse of forgetting the second index sends `a U ^ k x` to `a [x, -k, A(x) - k]`. -/
@[simp]
theorem knotInfinityAlexanderLift_single_C_mul_T (x : H.Generator) (k : ℤ) (a : ZMod 2) :
    H.knotInfinityAlexanderLift A (Finsupp.single x (LaurentPolynomial.C a * T k)) =
      Finsupp.single (x, -k, A x - k) a := by
  rw [← single_eq_C_mul_T]
  simp only [knotInfinityAlexanderLift, Finsupp.lsum_single, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The inverse of forgetting the second index takes its values in `CFK^∞`. -/
theorem knotInfinityAlexanderLift_mem (c : H.Generator →₀ (ZMod 2)[T;T⁻¹]) :
    H.knotInfinityAlexanderLift A c ∈ H.knotInfinityAlexanderSubmodule A := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add]; exact add_mem hc hd
  | single x p =>
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [Finsupp.single_add, map_add]; exact add_mem hp hq
    | C_mul_T k a =>
      rw [knotInfinityAlexanderLift_single_C_mul_T]
      exact Finsupp.single_mem_supported _ _ (by simp)

/-- Forgetting the second index undoes `TauCeti.HeegaardRegionSystem.knotInfinityAlexanderLift`. -/
@[simp]
theorem knotInfinityForget_knotInfinityAlexanderLift (c : H.Generator →₀ (ZMod 2)[T;T⁻¹]) :
    H.knotInfinityForget (H.knotInfinityAlexanderLift A c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single x p =>
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [Finsupp.single_add, map_add, map_add, hp, hq]
    | C_mul_T k a =>
      rw [knotInfinityAlexanderLift_single_C_mul_T, knotInfinityForget_single, neg_neg,
        Finsupp.smul_single, LaurentPolynomial.smul_eq_C_mul]

/-- On `CFK^∞`, `TauCeti.HeegaardRegionSystem.knotInfinityAlexanderLift` undoes forgetting the
second index. -/
theorem knotInfinityAlexanderLift_knotInfinityForget {c : H.Generator × ℤ × ℤ →₀ ZMod 2}
    (hc : c ∈ H.knotInfinityAlexanderSubmodule A) :
    H.knotInfinityAlexanderLift A (H.knotInfinityForget c) = c := by
  rw [knotInfinityAlexanderSubmodule, Finsupp.supported_eq_span_single] at hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨⟨x, i, j⟩, hg, rfl⟩ := hc
    have hT : (T (-i) : (ZMod 2)[T;T⁻¹]) = LaurentPolynomial.C 1 * T (-i) := by simp
    rw [knotInfinityForget_single, one_smul, hT, knotInfinityAlexanderLift_single_C_mul_T, neg_neg]
    simp only [Set.mem_ofPred_eq] at hg
    dsimp only
    rw [show A x - -i = j by omega]
  | zero => simp
  | add _ _ _ _ hc hd => rw [map_add, map_add, hc, hd]
  | smul _ _ _ hc => rw [map_smul, map_smul, hc]

variable (H) in
/-- **`CFK^∞` is `CF^∞` of the ambient manifold.** For an Alexander grading `A`, forgetting the
second index is a linear isomorphism from the chains of `CFK^∞` (those on the cells with
`j - i = A(x)`) onto the chains of `CF^∞`, with inverse `U ^ k x ↦ [x, -k, A(x) - k]`. -/
noncomputable def knotInfinityAlexanderEquiv (A : H.Generator → ℤ) :
    H.knotInfinityAlexanderSubmodule A ≃ₗ[ZMod 2] H.Generator →₀ (ZMod 2)[T;T⁻¹] where
  toFun c := H.knotInfinityForget c
  invFun c := ⟨H.knotInfinityAlexanderLift A c, knotInfinityAlexanderLift_mem c⟩
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _
  left_inv c := Subtype.ext (knotInfinityAlexanderLift_knotInfinityForget c.property)
  right_inv c := knotInfinityForget_knotInfinityAlexanderLift c

@[simp]
theorem knotInfinityAlexanderEquiv_apply (c : H.knotInfinityAlexanderSubmodule A) :
    H.knotInfinityAlexanderEquiv A c = H.knotInfinityForget c :=
  (rfl)

@[simp]
theorem coe_knotInfinityAlexanderEquiv_symm_apply (c : H.Generator →₀ (ZMod 2)[T;T⁻¹]) :
    ((H.knotInfinityAlexanderEquiv A).symm c : H.Generator × ℤ × ℤ →₀ ZMod 2) =
      H.knotInfinityAlexanderLift A c :=
  (rfl)

/-- **The action of `U`.** The isomorphism `TauCeti.HeegaardRegionSystem.knotInfinityAlexanderEquiv`
turns the shift by `(a, a)` of `CFK^∞` into multiplication by `U ^ a` on `CF^∞`. -/
theorem knotInfinityAlexanderEquiv_knotInfinityShift (a : ℤ)
    (c : H.knotInfinityAlexanderSubmodule A) :
    H.knotInfinityAlexanderEquiv A ⟨H.knotInfinityShift a a c,
      knotInfinityShift_mem_knotInfinityAlexanderSubmodule_iff.mpr c.property⟩ =
      (T a : (ZMod 2)[T;T⁻¹]) • H.knotInfinityAlexanderEquiv A c := by
  rw [knotInfinityAlexanderEquiv_apply, knotInfinityAlexanderEquiv_apply,
    knotInfinityForget_knotInfinityShift]

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

variable {χ : Region → ℤ} {w z : Basepoint}

/-- **`CFK^∞` and `CF^∞` are isomorphic complexes.** For an Alexander grading `A` with
`A(x) - A(y) = n_z(D) - n_w(D)` for every domain `D` from `x` to `y`, the isomorphism
`TauCeti.HeegaardRegionSystem.knotInfinityAlexanderEquiv` intertwines the infinity knot
differential restricted to `CFK^∞` with the infinity differential of the diagram pointed at `w`
alone. -/
theorem knotInfinityAlexanderEquiv_restrict_knotInfinityDifferential
    (hA : ∀ {x y : H.Generator} {D : Region → ℤ}, H.IsDomainBetween x y D →
      A x - A y = D (H.basepoint z) - D (H.basepoint w))
    (c : H.knotInfinityAlexanderSubmodule A) :
    H.knotInfinityAlexanderEquiv A ((H.knotInfinityDifferential χ w z).restrict
      (knotInfinityAlexanderSubmodule_le_comap_knotInfinityDifferential hA) c) =
      (H.withBasepoints fun _ : Unit => H.basepoint w).infinityDifferential χ
        (H.knotInfinityAlexanderEquiv A c) := by
  simp [LinearMap.restrict_apply, knotInfinityForget_knotInfinityDifferential]

end AlexanderEquiv

end HeegaardRegionSystem

end TauCeti
