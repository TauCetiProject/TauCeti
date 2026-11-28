/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.Topology.Instances.AddCircle.StraightCircle
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Genus-one Heegaard diagrams with straight attaching circles

On the torus `T² = ℝ² / ℤ²` (`UnitAddTorus (Fin 2)`), let `α` and `β` be the straight circles of
directions `u` and `v`, integer vectors with coprime coordinates, so that both are embedded circles
through `0` (`TauCeti.straightCircleHom`). Together with a basepoint off `α ∪ β` they form a
genus-one Heegaard diagram. For `u = (1, 0)` and `v = (q, p)` it is the standard diagram of the
lens space `L(p, q)`, for `v = (0, 1)` that of `S³`; in general the represented manifold has
`H₁ = H₁(T²) / ⟨[α], [β]⟩ = ℤ² / ⟨u, v⟩`, the classes of `α` and `β` being their directions.

In genus one the tori `T_α` and `T_β` of the symmetric product are the curves themselves, so the
generators of the Heegaard Floer complex are the intersection points of `α` and `β`, the subgroup
`TauCeti.straightDiagramGenerators u v` of `T²`. They are counted by the determinant: there are
`|u₀ v₁ - u₁ v₀|` of them (`TauCeti.natCard_straightDiagramGenerators`), infinitely many when the
curves are parallel, since they then coincide.

For two generators `x` and `y`, Ozsváth and Szabó's class `ε(x, y)` is the class of the loop
running from `x` to `y` along `α` and back from `y` to `x` along `β`, in
`H₁(T²) / ⟨[α], [β]⟩`. Lift the arc of `α` to the segment from a lift of `x` to it plus `s u`, and
the arc of `β` to the segment from there on by `t v`; the loop closes up in `T²`, so `s u + t v` is
an integer vector `n`, the class of the loop in `H₁(T²) = ℤ²`, and `ε(x, y)` is its class in
`ℤ² / ⟨u, v⟩` (`TauCeti.straightDiagramEpsilon_eq`). Changing the arcs by whole turns changes `n`
by multiples of `u` and `v`. Here `ε` is defined as `ε(x, y) = E (y - x)` for the isomorphism
`E = TauCeti.straightCircleInfQuotientEquiv` of the generators with `ℤ² / ⟨u, v⟩`
(`TauCeti.straightDiagramEpsilon_def`), which reads the displacement of the loop through `0` and
`y - x`. Consequently:

* `ε(x, y) + ε(y, w) = ε(x, w)` (`TauCeti.straightDiagramEpsilon_add_straightDiagramEpsilon`);
* `ε(x, y) = 0` in `ℤ² / ⟨u, v⟩` only for `x = y` (`TauCeti.straightDiagramEpsilon_eq_zero_iff`);
* `y ↦ ε(x, y)` is a bijection from the generators onto `ℤ² / ⟨u, v⟩`
  (`TauCeti.straightDiagramEpsilon_bijective`).

These are statements about classes in `ℤ² / ⟨u, v⟩` only. Informally, through the identification
of `ℤ² / ⟨u, v⟩` with `H₁` of the represented manifold and Ozsváth and Szabó's correspondence
between `ε` and spin^c structures, they say that distinct generators lie in distinct spin^c
structures, so that no Whitney disc joins two of them, and that each spin^c structure carries
exactly one generator; neither the identification nor the correspondence is formalized here.

These are the geometric counterparts, for these diagrams, of the statements about the incidence
data `TauCeti.HeegaardRegionSystem.lensSpace` proved in
`TauCeti.LowDimTopology.Heegaard.LensSpace.Diagram`. The identification of `ℤ² / ⟨u, v⟩` with the
first homology of the represented three-manifold, by the Mayer–Vietoris sequence, is not
formalized here.

For the lens space diagram, `u = (1, 0)` and `v = (q, p)` with `p ≠ 0` coprime to `q`,
`ℤ² / ⟨u, v⟩` is `ℤ/p` through the second coordinate (`TauCeti.lensQuotientEquiv`). The examples
`(1, 0), (0, 1)` with its single generator and `(1, 0), (1, 3)` with its three generators are
worked out at the end: in the second, the generator `y = [(1/3, 0)]` has
`ε(0, y) = 2` and `ε(y, 0) = 1` in `ℤ/3` (`TauCeti.lensQuotientEquiv_straightDiagramEpsilon_three`).

## Main definitions

* `TauCeti.straightDiagramGenerators`: the intersection points of the straight circles.
* `TauCeti.straightDiagramEpsilon`: the class `ε(x, y) ∈ ℤ² / ⟨u, v⟩` of two generators.
* `TauCeti.lensQuotientEquiv`: `ℤ² / ⟨(1, 0), (q, p)⟩ ≃ ℤ/p`.

## Main results

* `TauCeti.natCard_straightDiagramGenerators`: there are `|u₀ v₁ - u₁ v₀|` generators.
* `TauCeti.straightDiagramEpsilon_eq`: `ε(x, y)` is the class of the lattice displacement of a
  loop along `α` from `x` to `y` and back along `β`.
* `TauCeti.straightDiagramEpsilon_add_straightDiagramEpsilon`,
  `TauCeti.straightDiagramEpsilon_eq_zero_iff`, `TauCeti.straightDiagramEpsilon_bijective`: `ε`
  is additive and sorts the generators bijectively into the classes of `ℤ² / ⟨u, v⟩`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.4 (Definition 2.11 of `ε(x, y)`)
  and §3.1 (the genus-one diagrams of lens spaces).
-/

public section

noncomputable section

namespace TauCeti

variable (u v : Fin 2 → ℤ)

/-- The generators of the genus-one Heegaard diagram on `T² = ℝ² / ℤ²` whose attaching circles are
the straight circles `α` and `β` of directions `u` and `v`: the intersection points of `α` and
`β`, a subgroup of the torus. -/
abbrev straightDiagramGenerators : AddSubgroup (UnitAddTorus (Fin 2)) :=
  straightCircle UnitAddCircle u ⊓ straightCircle UnitAddCircle v

theorem mem_straightDiagramGenerators_iff {x : UnitAddTorus (Fin 2)} :
    x ∈ straightDiagramGenerators u v ↔
      (∃ σ, straightCircleHom UnitAddCircle u σ = x) ∧
        ∃ τ, straightCircleHom UnitAddCircle v τ = x :=
  AddSubgroup.mem_inf

/-- **The number of generators.** A genus-one diagram with straight attaching circles of primitive
directions `u` and `v` has `|u₀ v₁ - u₁ v₀|` generators. When the directions are parallel the
curves coincide, there are infinitely many, and `Nat.card` takes the junk value `0`. -/
theorem natCard_straightDiagramGenerators {u v : Fin 2 → ℤ} (hu : IsCoprime (u 0) (u 1))
    (hv : IsCoprime (v 0) (v 1)) :
    Nat.card (straightDiagramGenerators u v) = (u 0 * v 1 - u 1 * v 0).natAbs :=
  natCard_straightCircle_inf 1 one_ne_zero hu hv

section Epsilon

variable {u v} (hu : IsCoprime (u 0) (u 1)) (hv : IsCoprime (v 0) (v 1))
  (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0)

/-- The class `ε(x, y) ∈ ℤ² / ⟨u, v⟩` of two generators `x` and `y` of the genus-one diagram with
straight attaching circles of directions `u` and `v`: the class of a loop from `x` to `y` along `α`
and back along `β` (`TauCeti.straightDiagramEpsilon_eq`). -/
def straightDiagramEpsilon (x y : straightDiagramGenerators u v) :
    (Fin 2 → ℤ) ⧸ (Submodule.span ℤ {u, v}).toAddSubgroup :=
  straightCircleInfQuotientEquiv 1 one_ne_zero hu hv hdet (y - x)

/-- `ε(x, y)` is the class of `y - x` under the isomorphism
`TauCeti.straightCircleInfQuotientEquiv` of the generators with `ℤ² / ⟨u, v⟩`. -/
theorem straightDiagramEpsilon_def (x y : straightDiagramGenerators u v) :
    straightDiagramEpsilon hu hv hdet x y =
      straightCircleInfQuotientEquiv 1 one_ne_zero hu hv hdet (y - x) :=
  (rfl)

/-- **`ε(x, y)` is the lattice displacement of a loop.** Let `s`, `t` be real and `n` integral with
`s u + t v = n`. If moving `x` by `s` along the direction `u` reaches `y`, then moving `y` by `t`
along the direction `v` returns to `x` (`TauCeti.straightCircleHom_add_straightCircleHom_eq_zero`),
and `ε(x, y)` is the class of `n`. -/
theorem straightDiagramEpsilon_eq {x y : straightDiagramGenerators u v} {s t : ℝ}
    {n : Fin 2 → ℤ} (hn : ∀ i, s * u i + t * v i = n i)
    (hxy : (x : UnitAddTorus (Fin 2)) + straightCircleHom UnitAddCircle u (s : UnitAddCircle) = y) :
    straightDiagramEpsilon hu hv hdet x y = QuotientAddGroup.mk n :=
  straightCircleInfQuotientEquiv_apply 1 one_ne_zero hu hv hdet (y - x) hn
    (by rw [mul_one, AddSubgroup.coe_sub, ← hxy, add_sub_cancel_left])

@[simp]
theorem straightDiagramEpsilon_self (x : straightDiagramGenerators u v) :
    straightDiagramEpsilon hu hv hdet x x = 0 := by
  rw [straightDiagramEpsilon_def, sub_self, map_zero]

/-- `ε(x, y) + ε(y, w) = ε(x, w)`. -/
@[simp]
theorem straightDiagramEpsilon_add_straightDiagramEpsilon (x y w : straightDiagramGenerators u v) :
    straightDiagramEpsilon hu hv hdet x y + straightDiagramEpsilon hu hv hdet y w =
      straightDiagramEpsilon hu hv hdet x w := by
  rw [straightDiagramEpsilon_def, straightDiagramEpsilon_def, straightDiagramEpsilon_def, ← map_add,
    sub_add_sub_cancel']

@[simp]
theorem neg_straightDiagramEpsilon (x y : straightDiagramGenerators u v) :
    -straightDiagramEpsilon hu hv hdet x y = straightDiagramEpsilon hu hv hdet y x := by
  rw [straightDiagramEpsilon_def, straightDiagramEpsilon_def, ← map_neg, neg_sub]

/-- **Distinct generators have distinct classes.** `ε(x, y) = 0` exactly when `x = y`. -/
@[simp]
theorem straightDiagramEpsilon_eq_zero_iff {x y : straightDiagramGenerators u v} :
    straightDiagramEpsilon hu hv hdet x y = 0 ↔ x = y := by
  rw [straightDiagramEpsilon_def, AddEquivClass.map_eq_zero_iff, sub_eq_zero, eq_comm]

/-- **One generator in each class.** For every generator `x`, `y ↦ ε(x, y)` is a bijection from
the generators onto `ℤ² / ⟨u, v⟩`. -/
theorem straightDiagramEpsilon_bijective (x : straightDiagramGenerators u v) :
    Function.Bijective (straightDiagramEpsilon hu hv hdet x) :=
  (straightCircleInfQuotientEquiv 1 one_ne_zero hu hv hdet).bijective.comp
    (Equiv.subRight x).bijective

end Epsilon

/-! ### Lens space diagrams -/

section Lens

variable (p : ℕ) (q : ℤ)

/-- An integer vector lies in the lattice spanned by `(1, 0)` and `(q, p)` exactly when its second
coordinate is divisible by `p`. -/
theorem mem_span_lens_iff {n : Fin 2 → ℤ} :
    n ∈ Submodule.span ℤ {![1, 0], ![q, (p : ℤ)]} ↔ (p : ℤ) ∣ n 1 := by
  rw [Submodule.mem_span_pair]
  refine ⟨fun ⟨c, d, h⟩ ↦ ⟨d, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨n 0 - k * q, k, ?_⟩⟩
  · rw [← h]
    simp [mul_comm]
  · ext i
    fin_cases i <;> simp [hk, mul_comm]

/-- The quotient of `ℤ²` by the lattice spanned by `(1, 0)` and `(q, p)` is `ℤ/p`, through the
second coordinate (`TauCeti.lensQuotientEquiv_mk`). For `u = (1, 0)` and `v = (q, p)` it is the
first homology `ℤ/p` of the lens space `L(p, q)` presented by the diagram. -/
def lensQuotientEquiv :
    (Fin 2 → ℤ) ⧸ (Submodule.span ℤ {![1, 0], ![q, (p : ℤ)]}).toAddSubgroup ≃+ ZMod p :=
  let φ : (Fin 2 → ℤ) →+ ZMod p := (Int.castAddHom (ZMod p)).comp (Pi.evalAddMonoidHom _ 1)
  have hφ : Function.Surjective φ := fun z ↦ by
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨![0, k], by simp [φ]⟩
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext n
    rw [Submodule.mem_toAddSubgroup, mem_span_lens_iff, AddMonoidHom.mem_ker,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [φ])).trans (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ)

@[simp]
theorem lensQuotientEquiv_mk (n : Fin 2 → ℤ) :
    lensQuotientEquiv p q (QuotientAddGroup.mk n) = n 1 := by
  rw [lensQuotientEquiv, AddEquiv.trans_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  exact (QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk _ _ n).trans (by simp)

variable {p q}

/-- **The generators of a lens space diagram.** The genus-one diagram with straight attaching
circles of directions `(1, 0)` and `(q, p)`, `q` coprime to `p`, has `p` generators. -/
theorem natCard_straightDiagramGenerators_lens (hpq : IsCoprime q p) :
    Nat.card (straightDiagramGenerators ![1, 0] ![q, (p : ℤ)]) = p := by
  rw [natCard_straightDiagramGenerators isCoprime_one_left (by simpa using hpq)]
  simp

/-- **The generators of a lens space diagram are the elements of `ℤ/p`.** For the diagram with
straight attaching circles of directions `(1, 0)` and `(q, p)`, `p ≠ 0` and `q` coprime to `p`, and
any generator `x`, the classes `ε(x, y) ∈ ℤ/p` of the generators `y` are the elements of `ℤ/p`, each
exactly once. -/
theorem lensQuotientEquiv_comp_straightDiagramEpsilon_bijective (hpq : IsCoprime q p) (hp : p ≠ 0)
    (x : straightDiagramGenerators ![1, 0] ![q, (p : ℤ)]) :
    Function.Bijective (lensQuotientEquiv p q ∘
      straightDiagramEpsilon isCoprime_one_left (by simpa using hpq) (by simpa using hp) x) :=
  (lensQuotientEquiv p q).bijective.comp (straightDiagramEpsilon_bijective _ _ _ x)

end Lens

/-! ### Examples -/

/-- The genus-one diagram of `S³`, with straight attaching circles of directions `(1, 0)` and
`(0, 1)`, has a single generator. -/
theorem natCard_straightDiagramGenerators_sphere :
    Nat.card (straightDiagramGenerators ![1, 0] ![0, 1]) = 1 := by
  simpa using natCard_straightDiagramGenerators_lens (p := 1) (q := 0) isCoprime_one_right

/-- The point `[(1/3, 0)]` is a generator of the diagram of `L(3, 1)` with straight attaching
circles of directions `(1, 0)` and `(1, 3)`. -/
theorem mem_straightDiagramGenerators_three :
    (fun i ↦ ((![1 / 3, 0] i : ℝ) : UnitAddCircle)) ∈
      straightDiagramGenerators ![1, 0] ![1, 3] := by
  -- `3 • [1/3] = [1] = 0` in `ℝ / ℤ`.
  have h3 : (3 : ℤ) • ((3⁻¹ : ℝ) : UnitAddCircle) = 0 := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    norm_num
  refine (mem_straightDiagramGenerators_iff _ _).2 ⟨⟨((1 / 3 : ℝ) : UnitAddCircle), ?_⟩,
    ((1 / 3 : ℝ) : UnitAddCircle), ?_⟩ <;> ext i <;> fin_cases i <;> simp [h3]

/-- **The classes `ε` in the diagram of `L(3, 1)`.** In the diagram with straight attaching circles
of directions `(1, 0)` and `(1, 3)`, let `y = [(1/3, 0)]`. The arc of `α` from `0` to `y` lifts to
the displacement `(1/3, 0)` and the arc of `β` back to `0` to `(-1/3, -1)`, of sum `(0, -1)`. So
in `ℤ² / ⟨(1, 0), (1, 3)⟩ = ℤ/3`, read through the second coordinate, `ε(0, y) = -1 = 2`, and
`ε(y, 0) = 1`. -/
theorem lensQuotientEquiv_straightDiagramEpsilon_three
    {y : straightDiagramGenerators ![1, 0] ![1, 3]}
    (hy : (y : UnitAddTorus (Fin 2)) = fun i ↦ ((![1 / 3, 0] i : ℝ) : UnitAddCircle)) :
    lensQuotientEquiv 3 1 (straightDiagramEpsilon (by simp [isCoprime_one_left])
        (by simp [isCoprime_one_left]) (by simp) 0 y) = 2 ∧
      lensQuotientEquiv 3 1 (straightDiagramEpsilon (by simp [isCoprime_one_left])
        (by simp [isCoprime_one_left]) (by simp) y 0) = 1 := by
  have h : straightDiagramEpsilon (by simp [isCoprime_one_left]) (by simp [isCoprime_one_left])
      (by simp) 0 y =
      QuotientAddGroup.mk ![0, -1] := by
    refine straightDiagramEpsilon_eq _ _ _ (s := 1 / 3) (t := -1 / 3) (fun i ↦ ?_) ?_
    · fin_cases i <;> norm_num
    · rw [hy]
      ext i
      fin_cases i <;> simp
  rw [← neg_straightDiagramEpsilon _ _ _ 0 y, h, ← QuotientAddGroup.mk_neg, lensQuotientEquiv_mk,
    lensQuotientEquiv_mk]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply, Int.cast_neg, Int.cast_one,
    neg_neg]
  decide

end TauCeti
