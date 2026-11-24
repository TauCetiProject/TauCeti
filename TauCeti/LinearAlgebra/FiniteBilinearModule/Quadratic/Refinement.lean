/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Basic
import TauCeti.Algebra.Group.Pow
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Quadratic refinements of symmetric pairings

Every symmetric pairing `b : A × A → ℚ/ℤ` on a finite abelian group `A` has a quadratic
refinement: a quadratic map `q : A → ℚ/ℤ`, homogeneous in the sense `q(m x) = m² q(x)`, whose polar
form is `b`. Write `A ≅ ∏ ℤ/nᵢ` and let `gᵢ` be the image of the `i`-th basis vector of `ℤ^ι`.
Order the indices, and choose `cᵢ` with `2cᵢ = b(gᵢ, gᵢ)` and `nᵢ²cᵢ = 0`; this is possible
because `nᵢ b(gᵢ, gᵢ) = 0`. The upper-triangular quadratic map

```text
Q(k) = ∑ᵢ kᵢ² cᵢ + ∑_{i < j} kᵢ kⱼ b(gᵢ, gⱼ)
```

on `ℤ^ι` has polar form `b(∑ kᵢ gᵢ, ∑ lⱼ gⱼ)` and vanishes on the kernel `∏ nᵢℤ` of
`k ↦ ∑ kᵢ gᵢ`, so it descends to `A`. Through such a refinement, statements about finite quadratic
modules, such as Nikulin's generator decomposition, pass to symmetric pairings. The refinement is
not unique in general: on `ℤ/2` with `b(1, 1) = 1/2` the values `q(1) = 1/4` and `q(1) = 3/4` both
refine `b`.

In odd order the refinement is unique. On a finite abelian group `A` of odd order `n`, a symmetric
pairing `b` has exactly one quadratic refinement, the map

```text
q(x) = ((n + 1) / 2) · b(x, x).
```

Indeed every quadratic map `q` with polar form `b` satisfies `2q(x) = b(x, x)` and `n q(x) = 0`,
so `q(x) = (n + 1) q(x) = ((n + 1) / 2) · b(x, x)`. Consequently a bilinear isometry between finite
quadratic modules of odd order preserves the quadratic maps, and finite quadratic modules of odd
order are classified by their bilinear modules alone.

## Main declarations

* `TauCeti.FiniteBilinearModule.exists_quadraticMap_polar_eq_pairing`: every symmetric pairing on a
  finite abelian group is the polar form of a quadratic map.
* `TauCeti.FiniteQuadraticModule.toFiniteBilinearModule_surjective`: every finite bilinear module
  is the bilinear module of a finite quadratic module.
* `TauCeti.FiniteBilinearModule.quadraticRefinement`: the quadratic refinement
  `x ↦ ((n + 1) / 2) · b(x, x)` of a finite bilinear module of odd order `n`.
* `TauCeti.FiniteQuadraticModule.quadratic_eq_nsmul_pairing_self_of_odd` and
  `TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`: every finite quadratic module of odd
  order is the quadratic refinement of its bilinear module.
* `TauCeti.FiniteQuadraticModule.map_quadratic_of_odd`,
  `TauCeti.FiniteQuadraticModule.homOfBilinearHomOfOdd`, and
  `TauCeti.FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd`: a bilinear morphism or
  isometry out of a finite quadratic module of odd order is a quadratic morphism or isometry.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`: finite quadratic
  modules of odd order are isometric exactly when their bilinear modules are.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti

universe u v w

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule.{u})

/-- **The quadratic refinement of a symmetric pairing of odd order.** On a finite abelian group
of odd order `n`, the quadratic map `x ↦ ((n + 1) / 2) • b(x, x)` has polar form `b`, since
`(n + 1) • b(x, y) = b(x, y)`. It is the only finite quadratic module structure with pairing `b`
(`TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`).

Exposed so that its bilinear module is `A` by definition, and bilinear isometries into or out of
`A` are bilinear isometries of the refinement. -/
@[expose] noncomputable def quadraticRefinement (hA : Odd (Nat.card A)) :
    FiniteQuadraticModule where
  toFiniteBilinearModule := A
  quadratic := LinearMap.BilinMap.toQuadraticMap (((Nat.card A + 1) / 2) • A.toBilin)
  polar_eq_pairing' x y := by
    have hn : Nat.card A • A.pairing x y = 0 := by
      rw [← pairing_nsmul_left, card_nsmul_eq_zero', pairing_zero_left]
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    simp only [LinearMap.smul_apply, toBilin_apply]
    rw [A.pairing_comm y x, ← smul_add, ← two_nsmul, nsmul_two_nsmul_of_odd hA hn]

/-- The bilinear module of the quadratic refinement of `A` is `A`. -/
@[simp]
theorem quadraticRefinement_toFiniteBilinearModule (hA : Odd (Nat.card A)) :
    (A.quadraticRefinement hA).toFiniteBilinearModule = A :=
  (rfl)

/-- The quadratic refinement of a pairing `b` on a group of odd order `n` is
`x ↦ ((n + 1) / 2) • b(x, x)`. -/
@[simp]
theorem quadraticRefinement_quadratic (hA : Odd (Nat.card A)) (x : A) :
    (A.quadraticRefinement hA).quadratic x = ((Nat.card A + 1) / 2) • A.pairing x x :=
  (LinearMap.BilinMap.toQuadraticMap_apply _ x).trans <| by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, toBilin_apply]

/-! ### Existence of quadratic refinements -/

/-- A half `c` of the self-pairing `b(x, x)` with `n² c = 0`, for `x` killed by `n`. For odd `n`
it is `((n + 1) / 2) b(x, x)`; for even `n` any half works. -/
private theorem exists_two_nsmul_eq_pairing_self {n : ℕ} {x : A} (hx : n • x = 0) :
    ∃ c : AddCircle (1 : ℚ), 2 • c = A.pairing x x ∧ n • n • c = 0 := by
  have hn : n • A.pairing x x = 0 := by rw [← pairing_nsmul_left, hx, pairing_zero_left]
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | hodd
  · have h2 : 2 • DivisibleBy.div (A.pairing x x) (2 : ℤ) = A.pairing x x := by
      rw [two_nsmul, ← two_zsmul, DivisibleBy.div_cancel _ two_ne_zero]
    have ht : (t + t) • DivisibleBy.div (A.pairing x x) (2 : ℤ) = t • A.pairing x x := by
      rw [← two_mul, mul_comm, mul_smul, h2]
    exact ⟨_, h2, by rw [ht, smul_comm, hn, smul_zero]⟩
  · exact ⟨((n + 1) / 2) • A.pairing x x, by rw [smul_comm, nsmul_two_nsmul_of_odd hodd hn],
      by rw [smul_comm n ((n + 1) / 2), hn, smul_zero, smul_zero]⟩

/-- **The upper-triangular quadratic map.** Let `g` be a finite family in `A`, indexed by a linearly
ordered type, with `nᵢ gᵢ = 0`. There is a quadratic map `Q` on `ℤ^ι` whose polar form is the
pairing of `A` read through `k ↦ ∑ kᵢ gᵢ`, and which vanishes on every `k` with `nᵢ ∣ kᵢ` for all
`i`. It is `Q(k) = ∑ᵢ kᵢ² cᵢ + ∑_{i < j} kᵢ kⱼ b(gᵢ, gⱼ)` for suitable halves `cᵢ` of
`b(gᵢ, gᵢ)`. -/
private theorem exists_quadraticMap_polar_eq_pairing_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (g : ι → A) (n : ι → ℕ) (hg : ∀ i, n i • g i = 0) :
    ∃ Q : QuadraticMap ℤ (ι → ℤ) (AddCircle (1 : ℚ)),
      (∀ x y, QuadraticMap.polar Q x y = A.pairing (∑ i, x i • g i) (∑ i, y i • g i)) ∧
        ∀ k : ι → ℤ, (∀ i, (n i : ℤ) ∣ k i) → Q k = 0 := by
  set b : ι → ι → AddCircle (1 : ℚ) := fun i j ↦ A.pairing (g i) (g j) with hb
  have hnb (i j : ι) : n i • b i j = 0 := by
    rw [hb, ← pairing_nsmul_left, hg, pairing_zero_left]
  choose c hc2 hcn using fun i ↦ A.exists_two_nsmul_eq_pairing_self (hg i)
  set C : ι → ι → AddCircle (1 : ℚ) := fun i j ↦ if i < j then b i j else if i = j then c i else 0
    with hCdef
  have hC (i j : ι) : C i j + C j i = b i j := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hCdef, h, h.not_gt, h.ne']
    · simp [hCdef, ← two_nsmul, hc2, hb]
    · simp [hCdef, h, h.not_gt, h.ne', hb, A.pairing_comm (g i)]
  let B : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] AddCircle (1 : ℚ) := Matrix.toLinearMap₂' ℤ (Matrix.of C)
  refine ⟨LinearMap.BilinMap.toQuadraticMap B, fun x y ↦ ?_, fun k hk ↦ ?_⟩
  · -- The polar form is `∑ᵢ ∑ⱼ xᵢ yⱼ (C i j + C j i) = ∑ᵢ ∑ⱼ xᵢ yⱼ b(gᵢ, gⱼ)`.
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    calc B x y + B y x = ∑ i, ∑ j, x i • y j • (C i j + C j i) := by
          simp only [B, Matrix.toLinearMap₂'_apply, Matrix.of_apply, smul_add,
            Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j ↦ y i • x j • C i j)]
          simp only [smul_comm (y _) (x _)]
      _ = A.pairing (∑ i, x i • g i) (∑ i, y i • g i) := by
          simp only [hC, hb]
          rw [← toBilin_apply]
          simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, toBilin_apply,
            Finset.smul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _
  · -- Each term `kᵢ kⱼ C i j` vanishes, since `nᵢ b(gᵢ, gⱼ) = 0` and `nᵢ² cᵢ = 0`.
    choose m hm using hk
    rw [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply]
    refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
    simp only [Matrix.of_apply, hCdef]
    split_ifs with hij hij'
    · rw [hm i, mul_comm, mul_smul]
      simp [smul_comm (n i) (k j), hnb]
    · subst hij'
      rw [hm i, mul_comm, mul_smul, mul_smul]
      simp [smul_comm (n i : ℤ) (m i), hcn]
    · simp

/-- **Existence of quadratic refinements.** Every symmetric pairing `b` on a finite abelian group
is the polar form of a quadratic map `q : A → ℚ/ℤ`, that is, `q(x + y) - q(x) - q(y) = b(x, y)` and
`q(m x) = m² q(x)`. The refinement is unique in odd order
(`TauCeti.FiniteQuadraticModule.eq_quadraticRefinement`) but not in general. -/
theorem exists_quadraticMap_polar_eq_pairing :
    ∃ q : QuadraticMap ℤ A (AddCircle (1 : ℚ)),
      ∀ x y, QuadraticMap.polar q x y = A.pairing x y := by
  -- Present `A ≅ ∏ ℤ/nᵢ` as the quotient of `ℤ^ι` by `∏ nᵢℤ`.
  obtain ⟨ι, _, p, -, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  let n : ι → ℕ := fun i ↦ p i ^ e i
  let g : A ≃+ ((i : ι) → ZMod (n i)) :=
    f.trans (DirectSum.linearEquivFunOnFintype ℤ ι fun i ↦ ZMod (n i)).toAddEquiv
  let π : (ι → ℤ) →+ A := g.symm.toAddMonoidHom.comp
    (AddMonoidHom.pi fun i ↦ (Int.castAddHom (ZMod (n i))).comp (Pi.evalAddMonoidHom _ i))
  have hπ_apply (k : ι → ℤ) : g (π k) = fun i ↦ (k i : ZMod (n i)) := by
    ext i
    simp [π]
  have hker (k : ι → ℤ) : π k = 0 ↔ ∀ i, (n i : ℤ) ∣ k i := by
    rw [← g.map_eq_zero_iff, hπ_apply, funext_iff]
    simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hπ : Function.Surjective π := fun a ↦ by
    choose k hk using fun i ↦ ZMod.intCast_surjective (g a i)
    exact ⟨k, g.injective (by rw [hπ_apply]; exact funext hk)⟩
  have hsum (k : ι → ℤ) : ∑ i, k i • π (Pi.single i 1) = π k := by
    simp_rw [← map_zsmul, ← map_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hg (i : ι) : n i • π (Pi.single i 1) = 0 := by
    rw [← map_nsmul, hker]
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  obtain ⟨Q, hpolar, hQ⟩ := exists_quadraticMap_polar_eq_pairing_sum A _ n hg
  have hpolar' (x y : ι → ℤ) : QuadraticMap.polar Q x y = A.pairing (π x) (π y) := by
    rw [hpolar, hsum, hsum]
  -- `Q` vanishes on the kernel of `π`, and so does its polar form, so `Q` descends to `A`.
  have hrad : LinearMap.ker π.toIntLinearMap ≤ Q.radical := fun k hk ↦ by
    have hk' : π k = 0 := LinearMap.mem_ker.1 hk
    exact ⟨hQ k ((hker k).1 hk'), LinearMap.ext fun y ↦ by
      rw [QuadraticMap.polarBilin_apply_apply, hpolar', hk', pairing_zero_left,
        LinearMap.zero_apply]⟩
  let q := Q.liftOfSurjective π.toIntLinearMap hπ hrad
  have hq (x : ι → ℤ) : q (π x) = Q x := Q.liftOfSurjective_apply π.toIntLinearMap hπ hrad x
  refine ⟨q, fun a a' ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hπ a
  obtain ⟨y, rfl⟩ := hπ a'
  rw [← hpolar']
  simp only [QuadraticMap.polar, ← map_add, hq]

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- On a finite quadratic module of odd order `n`, the quadratic map is determined by the pairing:
`q(x) = ((n + 1) / 2) • b(x, x)`. -/
theorem quadratic_eq_nsmul_pairing_self_of_odd (hA : Odd (Nat.card A)) (x : A) :
    A.quadratic x = ((Nat.card A + 1) / 2) • A.toFiniteBilinearModule.pairing x x := by
  rw [← polar_eq_pairing, QuadraticMap.polar_self,
    nsmul_two_nsmul_of_odd hA (A.natCard_nsmul_quadratic_of_odd hA x)]

/-- **Uniqueness of the quadratic refinement in odd order.** A finite quadratic module of odd
order is the quadratic refinement of its bilinear module. -/
theorem eq_quadraticRefinement (A : FiniteQuadraticModule.{u}) (hA : Odd (Nat.card A)) :
    A = A.toFiniteBilinearModule.quadraticRefinement hA := by
  obtain ⟨B, q, hq⟩ := A
  congr 1
  ext x
  exact (quadratic_eq_nsmul_pairing_self_of_odd (A := ⟨B, q, hq⟩) hA x).trans
    (B.quadraticRefinement_quadratic hA x).symm

/-- **Out of an odd-order module, a bilinear morphism is automatically a quadratic morphism.**
No nondegeneracy or codomain cardinality hypothesis is required, and the underlying map is
unchanged. -/
def homOfBilinearHomOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    Hom A B where
  toLinearMap := f.toAddMonoidHom.toIntLinearMap
  map_app' x := by
    rw [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap,
      FiniteBilinearModule.Hom.coe_toAddMonoidHom, ← sub_eq_zero]
    refine (nsmul_eq_zero_iff_of_coprime hA.coprime_two_left).mp ⟨?_, ?_⟩
    · rw [nsmul_sub, ← QuadraticMap.polar_self, ← QuadraticMap.polar_self,
        A.polar_eq_pairing, B.polar_eq_pairing, f.map_pairing, sub_self]
    · rw [nsmul_sub,
        B.nsmul_quadratic_of_odd hA (f x) (by rw [← map_nsmul, card_nsmul_eq_zero', map_zero]),
        A.natCard_nsmul_quadratic_of_odd hA, sub_self]

/-- Upgrading a bilinear morphism from an odd-order module preserves the underlying map. -/
@[simp]
theorem homOfBilinearHomOfOdd_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) (x : A) :
    homOfBilinearHomOfOdd hA f x = f x :=
  (rfl)

/-- Forgetting the quadratic structure after upgrading a bilinear morphism at odd order recovers
the original bilinear morphism. -/
@[simp]
theorem homOfBilinearHomOfOdd_toFiniteBilinearModule (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (homOfBilinearHomOfOdd hA f).toFiniteBilinearModule = f := by
  ext x; simp

/-- Upgrading the polar bilinear morphism of a quadratic morphism at odd order recovers the
quadratic morphism. -/
@[simp]
theorem toFiniteBilinearModule_homOfBilinearHomOfOdd (hA : Odd (Nat.card A)) (g : Hom A B) :
    homOfBilinearHomOfOdd hA g.toFiniteBilinearModule = g := by
  ext x; simp

/-- Upgrading the identity bilinear morphism at odd order gives the identity quadratic morphism. -/
@[simp]
theorem homOfBilinearHomOfOdd_id (A : FiniteQuadraticModule.{u}) (hA : Odd (Nat.card A)) :
    homOfBilinearHomOfOdd hA (FiniteBilinearModule.Hom.id A.toFiniteBilinearModule) =
      Hom.id A := by
  ext x; simp

/-- Upgrading a composite bilinear morphism at odd order gives the composite upgraded quadratic
morphism. -/
@[simp]
theorem homOfBilinearHomOfOdd_comp {C : FiniteQuadraticModule.{w}} (hA : Odd (Nat.card A))
    (hB : Odd (Nat.card B))
    (g : FiniteBilinearModule.Hom B.toFiniteBilinearModule C.toFiniteBilinearModule)
    (f : FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (homOfBilinearHomOfOdd hB g).comp (homOfBilinearHomOfOdd hA f) =
      homOfBilinearHomOfOdd hA (g.comp f) := by
  ext x; simp

/-- A bilinear isometry between finite quadratic modules of odd order preserves the quadratic
maps. -/
theorem map_quadratic_of_odd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : B.quadratic (f x) = A.quadratic x := by
  rw [← FiniteBilinearModule.Isometry.toHom_apply, ← homOfBilinearHomOfOdd_apply hA f.toHom]
  exact (homOfBilinearHomOfOdd hA f.toHom).map_app x

/-- A bilinear isometry between finite quadratic modules of odd order, as a quadratic isometry. -/
def isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    Isometry A B where
  toLinearEquiv := f.toAddEquiv.toIntLinearEquiv
  map_app' := map_quadratic_of_odd hA f

/-- The quadratic isometry `isometryOfBilinearIsometryOfOdd hA f` acts as `f`. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (x : A) : isometryOfBilinearIsometryOfOdd hA f x = f x :=
  (rfl)

/-- Evaluating the inverse of an odd-order upgraded bilinear isometry evaluates `f.symm`. -/
theorem isometryOfBilinearIsometryOfOdd_symm_apply (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (y : B) : (isometryOfBilinearIsometryOfOdd hA f).symm y = f.symm y := by
  apply EquivLike.injective f
  rw [← isometryOfBilinearIsometryOfOdd_apply hA f,
    QuadraticMap.IsometryEquiv.apply_symm_apply, f.apply_symm_apply]

/-- The inverse of a bilinear isometry upgraded at odd order is the upgraded inverse bilinear
isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_symm (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).symm =
      isometryOfBilinearIsometryOfOdd (Nat.card_congr f.toAddEquiv.toEquiv ▸ hA) f.symm :=
  DFunLike.ext _ _ fun y ↦ by
    rw [isometryOfBilinearIsometryOfOdd_symm_apply, isometryOfBilinearIsometryOfOdd_apply]

/-- Upgrading a bilinear isometry at odd order preserves its underlying additive equivalence. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_toAddEquiv (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toAddEquiv = f.toAddEquiv :=
  (rfl)

/-- Forgetting bijectivity of an odd-order upgraded bilinear isometry gives the upgraded bilinear
morphism. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_toHom (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toHom = homOfBilinearHomOfOdd hA f.toHom := by
  ext x
  rw [Isometry.toHom_apply, isometryOfBilinearIsometryOfOdd_apply,
    homOfBilinearHomOfOdd_apply, FiniteBilinearModule.Isometry.toHom_apply]

/-- Forgetting the quadratic maps of `isometryOfBilinearIsometryOfOdd hA f` recovers `f`. -/
@[simp]
theorem toFiniteBilinearModule_isometryOfBilinearIsometryOfOdd (hA : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).toFiniteBilinearModule = f :=
  -- Both sides have the additive equivalence `f.toAddEquiv`, repackaged as a `ℤ`-linear one.
  FiniteBilinearModule.Isometry.toAddEquiv_injective
    (Isometry.toFiniteBilinearModule_toAddEquiv _)

/-- Upgrading the polar bilinear isometry of a quadratic isometry at odd order recovers the
quadratic isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_toFiniteBilinearModule (hA : Odd (Nat.card A))
    (f : Isometry A B) :
    isometryOfBilinearIsometryOfOdd hA f.toFiniteBilinearModule = f :=
  DFunLike.ext _ _ fun x ↦
    (isometryOfBilinearIsometryOfOdd_apply hA f.toFiniteBilinearModule x).trans
      (DFunLike.congr_fun (Isometry.toFiniteBilinearModule_toAddEquiv f) x)

/-- Upgrading the identity bilinear isometry at odd order gives the identity quadratic isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_refl (A : FiniteQuadraticModule.{u})
    (hA : Odd (Nat.card A)) :
    isometryOfBilinearIsometryOfOdd hA
        (FiniteBilinearModule.Isometry.refl A.toFiniteBilinearModule) =
      QuadraticMap.IsometryEquiv.refl A.quadratic :=
  DFunLike.ext _ _ fun x ↦ by
    rw [isometryOfBilinearIsometryOfOdd_apply, FiniteBilinearModule.Isometry.refl_apply,
      ← Isometry.toHom_apply, Isometry.refl_toHom, Hom.id_apply]

/-- Upgrading a composite bilinear isometry at odd order gives the composite upgraded quadratic
isometry. -/
@[simp]
theorem isometryOfBilinearIsometryOfOdd_trans {C : FiniteQuadraticModule.{w}}
    (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (g : FiniteBilinearModule.Isometry B.toFiniteBilinearModule C.toFiniteBilinearModule) :
    (isometryOfBilinearIsometryOfOdd hA f).trans (isometryOfBilinearIsometryOfOdd hB g) =
      isometryOfBilinearIsometryOfOdd hA (f.trans g) :=
  DFunLike.ext _ _ fun x ↦ by simp

/-- Finite quadratic modules of odd order are isometric exactly when their bilinear modules are.
In odd order no Gauss-sum condition is needed, unlike Nikulin's comparison theorem
`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_and_gaussSign_eq`. -/
theorem nonempty_isometry_iff_bilinear_isometry_of_odd (hA : Odd (Nat.card A)) :
    Nonempty (Isometry A B) ↔
      Nonempty (FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toFiniteBilinearModule⟩, fun ⟨f⟩ ↦ ⟨isometryOfBilinearIsometryOfOdd hA f⟩⟩

/-- **Every symmetric pairing has a quadratic refinement**: every finite bilinear module is the
bilinear module of a finite quadratic module
(`TauCeti.FiniteBilinearModule.exists_quadraticMap_polar_eq_pairing`). -/
theorem toFiniteBilinearModule_surjective :
    Function.Surjective toFiniteBilinearModule.{u} := fun A ↦
  let ⟨q, hq⟩ := A.exists_quadraticMap_polar_eq_pairing
  ⟨⟨A, q, hq⟩, rfl⟩

end FiniteQuadraticModule

end TauCeti
