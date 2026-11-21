/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.AlgebraicGeometry.Chow.Basic
import TauCeti.Topology.KrullDimension.Basic
import TauCeti.Topology.LocallyFinsupp.Finsupp
import TauCeti.Topology.Sober

/-!
# Cycles on quasi-compact schemes and the Chow group in the top dimension

On a quasi-compact scheme `X` a cycle, having locally finite support, has finite support. Hence the
group `Z_k(X)` of `k`-cycles is the free abelian group on the points of dimension `k`, the generic
points of the integral closed subschemes of dimension `k`:

* `Chow.cyclesOfDimensionEquivFinsupp X k`: the identification of `Z_k(X)` with the finitely
  supported functions on the points of dimension `k`, reading off the coefficients;
* `Chow.cyclesOfDimensionBasis X k`: the basis of `Z_k(X)` given by the cycles `[x]` of the points
  `x` of dimension `k`.

Now let `X` be a locally Noetherian scheme of dimension at most `n`. It has no integral closed
subschemes of dimension `n + 1`, so no nonzero `n`-cycle is rationally equivalent to zero and the
class map `Z_n(X) → CH_n(X)` is an isomorphism (`Chow.cycleClassEquiv`). Moreover a point of
dimension `n` has no proper generization, so the points of dimension `n` are exactly the generic
points of the irreducible components of dimension `n`
(`Chow.mem_pointsOfDimension_iff_of_topologicalKrullDim_le`,
`Chow.pointsOfDimensionEquivIrreducibleComponents`). Together:

* `Chow.ChowGroup.basisOfTopologicalKrullDimLE`: for `X` moreover quasi-compact, `CH_n(X)` is free
  with basis the fundamental classes `[closure {x}]` of the `n`-dimensional irreducible components;
* `Chow.ChowGroup.finrank_eq_ncard_of_topologicalKrullDim_le`: for `X` Noetherian there are
  finitely many of them (`Chow.finite_pointsOfDimension_of_topologicalKrullDim_le`), and the rank
  of `CH_n(X)` is their number.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., Example 1.3.2.
* [The Stacks Project, Section 42.8](https://stacks.math.columbia.edu/tag/02QQ) for cycles.
-/

public section

open AlgebraicGeometry Order TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry.Chow

/-! ### Cycles on a quasi-compact scheme -/

section Compact

variable (X : Scheme.{u}) [CompactSpace X] (k : ℤ)

omit [CompactSpace X] in
/-- The cycle with coefficients given by a finitely supported function on the points of
dimension `k`, extended by zero. -/
private noncomputable def cycleOfFinsupp (f : pointsOfDimension X k →₀ ℤ) :
    cyclesOfDimension X k :=
  ⟨Function.locallyFinsupp.ofFinsupp (f.embDomain (Function.Embedding.subtype _)),
    mem_cyclesOfDimension_iff.mpr fun x hx ↦ by
      by_contra h
      exact hx <| (Function.locallyFinsupp.ofFinsupp_apply _ _).trans <|
        Finsupp.embDomain_of_notMem_range _ _ _ (by simpa using h)⟩

omit [CompactSpace X] in
private lemma cycleOfFinsupp_apply (f : pointsOfDimension X k →₀ ℤ) (x : pointsOfDimension X k) :
    (cycleOfFinsupp X k f : AlgebraicCycle X ℤ) x = f x :=
  (Function.locallyFinsupp.ofFinsupp_apply _ _).trans (Finsupp.embDomain_apply_self _ f x)

/-- On a quasi-compact scheme, the `k`-cycles are the finitely supported functions on the points
of dimension `k`: a cycle corresponds to its coefficients. -/
noncomputable def cyclesOfDimensionEquivFinsupp :
    cyclesOfDimension X k ≃ₗ[ℤ] (pointsOfDimension X k →₀ ℤ) :=
  AddEquiv.toIntLinearEquiv
    { toFun α := Finsupp.ofSupportFinite (fun x ↦ (α : AlgebraicCycle X ℤ) x)
        ((Function.locallyFinsupp.finite_support (α : AlgebraicCycle X ℤ)).preimage
          Subtype.val_injective.injOn)
      invFun := cycleOfFinsupp X k
      left_inv α := by
        refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
        by_cases h : x ∈ pointsOfDimension X k
        · exact cycleOfFinsupp_apply X k _ ⟨x, h⟩
        · rw [Function.notMem_support.mp fun hx ↦ h (mem_cyclesOfDimension_iff.mp α.2 hx)]
          exact Function.notMem_support.mp fun hx ↦
            h (mem_cyclesOfDimension_iff.mp (cycleOfFinsupp X k _).2 hx)
      right_inv f := Finsupp.ext (cycleOfFinsupp_apply X k f)
      map_add' _ _ := Finsupp.ext fun _ ↦ rfl }

/-- The coefficients of a cycle under `cyclesOfDimensionEquivFinsupp`. -/
@[simp]
lemma cyclesOfDimensionEquivFinsupp_apply (α : cyclesOfDimension X k)
    (x : pointsOfDimension X k) :
    cyclesOfDimensionEquivFinsupp X k α x = (α : AlgebraicCycle X ℤ) x :=
  (rfl)

/-- The cycle with given coefficients, under `cyclesOfDimensionEquivFinsupp`, at a point of
dimension `k`. -/
@[simp]
lemma cyclesOfDimensionEquivFinsupp_symm_apply (f : pointsOfDimension X k →₀ ℤ)
    (x : pointsOfDimension X k) :
    ((cyclesOfDimensionEquivFinsupp X k).symm f : AlgebraicCycle X ℤ) x = f x := by
  rw [← cyclesOfDimensionEquivFinsupp_apply, LinearEquiv.apply_symm_apply]

/-- The basis of the `k`-cycles on a quasi-compact scheme given by the cycles `[x]` of the points
of dimension `k` (`coe_cyclesOfDimensionBasis`). -/
noncomputable def cyclesOfDimensionBasis :
    Module.Basis (pointsOfDimension X k) ℤ (cyclesOfDimension X k) :=
  .ofRepr (cyclesOfDimensionEquivFinsupp X k)

/-- The coordinates of a cycle in `cyclesOfDimensionBasis` are its coefficients. -/
@[simp]
lemma cyclesOfDimensionBasis_repr_apply (α : cyclesOfDimension X k) (x : pointsOfDimension X k) :
    (cyclesOfDimensionBasis X k).repr α x = (α : AlgebraicCycle X ℤ) x :=
  (rfl)

/-- The basis vector of `cyclesOfDimensionBasis` at a point `x` of dimension `k` is the cycle `[x]`
with coefficient one at `x`. -/
@[simp]
lemma coe_cyclesOfDimensionBasis [DecidableEq X] (x : pointsOfDimension X k) :
    (cyclesOfDimensionBasis X k x : AlgebraicCycle X ℤ) =
      Function.locallyFinsuppWithin.single x.1 1 := by
  ext y
  rw [Function.locallyFinsuppWithin.single_apply]
  by_cases hy : y ∈ pointsOfDimension X k
  · rw [← cyclesOfDimensionBasis_repr_apply X k _ ⟨y, hy⟩,
      DFunLike.congr_fun ((cyclesOfDimensionBasis X k).repr_self x) ⟨y, hy⟩, Finsupp.single_apply]
    simp only [← Subtype.coe_inj, eq_comm]
  · have hne : y ≠ x.1 := fun h ↦ hy (h ▸ x.2)
    simp only [hne, ite_false]
    exact Function.notMem_support.mp fun h ↦
      hy (mem_cyclesOfDimension_iff.mp (cyclesOfDimensionBasis X k x).2 h)

end Compact

/-! ### The top dimension -/

section TopDimension

variable {X : Scheme.{u}} {n : ℕ}

/-- On a scheme of dimension at most `n`, the points of dimension `n` are the generic points of the
irreducible components of `X` of dimension `n`: such a point has no proper generization, which
would have larger dimension. -/
lemma mem_pointsOfDimension_iff_of_topologicalKrullDim_le (hX : topologicalKrullDim X ≤ n)
    {x : X} : x ∈ pointsOfDimension X n ↔ x ∈ genericPoints X ∧ height x = n := by
  refine ⟨fun hx ↦ ?_, fun h ↦ mem_pointsOfDimension.mpr ⟨n, h.2, rfl⟩⟩
  obtain ⟨m, hm, hmn⟩ := mem_pointsOfDimension.mp hx
  obtain rfl : m = n := by omega
  refine ⟨mem_genericPoints_iff.mpr fun y hy ↦ ?_, hm⟩
  by_contra hne
  -- A proper generization `y` of `x` is above `x` for the specialization order.
  have hxy : x < y := lt_of_le_not_ge hy fun h ↦ hne (hy.antisymm h).eq
  have := (height_strictMono hxy (by simp [hm])).trans_le
    (WithBot.coe_le_coe.mp ((height_le_topologicalKrullDim y).trans hX))
  simp [hm] at this

/-- On a scheme of dimension at most `n`, taking closures identifies the points of dimension `n`
with the irreducible components of dimension `n`. -/
noncomputable def pointsOfDimensionEquivIrreducibleComponents (hX : topologicalKrullDim X ≤ n) :
    pointsOfDimension X n ≃
      {Z : Set X // Z ∈ irreducibleComponents X ∧ topologicalKrullDim Z = n} :=
  ((Equiv.subtypeEquivRight fun _ ↦ mem_pointsOfDimension_iff_of_topologicalKrullDim_le hX).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm).trans <|
    (genericPoints.equiv.subtypeEquiv fun x ↦ by
      rw [← WithBot.coe_inj, height_eq_topologicalKrullDim_closure_singleton]
      norm_cast).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _)

/-- The irreducible component of dimension `n` corresponding to a point of dimension `n` is its
closure. -/
@[simp]
lemma coe_pointsOfDimensionEquivIrreducibleComponents_apply (hX : topologicalKrullDim X ≤ n)
    (x : pointsOfDimension X n) :
    (pointsOfDimensionEquivIrreducibleComponents hX x : Set X) = closure {x.1} :=
  (rfl)

/-- The closure of the point of dimension `n` corresponding to an irreducible component of
dimension `n` is that component. -/
@[simp]
lemma closure_pointsOfDimensionEquivIrreducibleComponents_symm_apply
    (hX : topologicalKrullDim X ≤ n)
    (Z : {Z : Set X // Z ∈ irreducibleComponents X ∧ topologicalKrullDim Z = n}) :
    closure {((pointsOfDimensionEquivIrreducibleComponents hX).symm Z : X)} = Z :=
  genericPoints.isGenericPoint_ofComponent ⟨Z.1, Z.2.1⟩

variable [IsLocallyNoetherian X]

/-- On a scheme of dimension at most `n`, no nonzero `n`-cycle is rationally equivalent to zero:
there are no integral closed subschemes of dimension `n + 1`. -/
lemma ratEquiv_eq_bot_of_topologicalKrullDim_le (hX : topologicalKrullDim X ≤ n) :
    RatEquiv X n = ⊥ :=
  ratEquiv_eq_bot_of_pointsOfDimension_eq_empty X <|
    Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
      obtain ⟨m, hm, hmn⟩ := mem_pointsOfDimension.mp hx
      have := (height_le_topologicalKrullDim x).trans hX
      rw [hm] at this
      norm_cast at this
      omega

/-- On a scheme of dimension at most `n`, the class map of `n`-cycles is injective. -/
lemma cycleClass_injective_of_topologicalKrullDim_le (hX : topologicalKrullDim X ≤ n) :
    Function.Injective (cycleClass : cyclesOfDimension X n → ChowGroup X n) :=
  (injective_iff_map_eq_zero _).mpr fun α hα ↦ by
    rwa [cycleClass_eq_zero_iff, ratEquiv_eq_bot_of_topologicalKrullDim_le hX,
      AddSubgroup.mem_bot] at hα

/-- On a scheme of dimension at most `n`, the class map identifies the `n`-cycles with the Chow
group `CH_n(X)`. -/
noncomputable def cycleClassEquiv (hX : topologicalKrullDim X ≤ n) :
    cyclesOfDimension X n ≃+ ChowGroup X n :=
  .ofBijective cycleClass ⟨cycleClass_injective_of_topologicalKrullDim_le hX,
    cycleClass_surjective⟩

/-- The isomorphism `cycleClassEquiv` is the class map. -/
@[simp]
lemma cycleClassEquiv_apply (hX : topologicalKrullDim X ≤ n) (α : cyclesOfDimension X n) :
    cycleClassEquiv hX α = cycleClass α :=
  (rfl)

/-- The inverse of `cycleClassEquiv` sends the class of an `n`-cycle back to the cycle. -/
@[simp]
lemma cycleClassEquiv_symm_cycleClass (hX : topologicalKrullDim X ≤ n)
    (α : cyclesOfDimension X n) : (cycleClassEquiv hX).symm (cycleClass α) = α :=
  (cycleClassEquiv hX).symm_apply_apply α

namespace ChowGroup

variable [CompactSpace X]

/-- On a quasi-compact scheme of dimension at most `n`, the Chow group `CH_n(X)` is free with
basis the classes of the cycles `[x]` of the points `x` of dimension `n`, that is, the fundamental
classes of the irreducible components of dimension `n`
(`pointsOfDimensionEquivIrreducibleComponents`). -/
noncomputable def basisOfTopologicalKrullDimLE (hX : topologicalKrullDim X ≤ n) :
    Module.Basis (pointsOfDimension X n) ℤ (ChowGroup X n) :=
  (cyclesOfDimensionBasis X n).map (cycleClassEquiv hX).toIntLinearEquiv

/-- The basis vector of `basisOfTopologicalKrullDimLE` at a point `x` is the class of the cycle
`[x]`. -/
@[simp]
lemma basisOfTopologicalKrullDimLE_apply (hX : topologicalKrullDim X ≤ n)
    (x : pointsOfDimension X n) :
    basisOfTopologicalKrullDimLE hX x = cycleClass (cyclesOfDimensionBasis X n x) :=
  (rfl)

/-- The coordinates of the class of a cycle in `basisOfTopologicalKrullDimLE` are its
coefficients. -/
@[simp]
lemma basisOfTopologicalKrullDimLE_repr_cycleClass (hX : topologicalKrullDim X ≤ n)
    (α : cyclesOfDimension X n) (x : pointsOfDimension X n) :
    (basisOfTopologicalKrullDimLE hX).repr (cycleClass α) x = (α : AlgebraicCycle X ℤ) x := by
  simp [basisOfTopologicalKrullDimLE, Module.Basis.map_repr]

/-- On a quasi-compact scheme of dimension at most `n`, the Chow group `CH_n(X)` is a free abelian
group. -/
lemma free_of_topologicalKrullDim_le (hX : topologicalKrullDim X ≤ n) :
    Module.Free ℤ (ChowGroup X n) :=
  .of_basis (basisOfTopologicalKrullDimLE hX)

end ChowGroup

end TopDimension

/-! ### Noetherian schemes -/

section Noetherian

variable {X : Scheme.{u}} {n : ℕ}

/-- A scheme of dimension at most `n` whose underlying space is Noetherian has finitely many points
of dimension `n`, being generic points of its finitely many irreducible components. -/
lemma finite_pointsOfDimension_of_topologicalKrullDim_le [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ n) : (pointsOfDimension X n).Finite :=
  (genericPoints.finite (NoetherianSpace.finite_irreducibleComponents (α := X))).subset
    fun _ hx ↦ ((mem_pointsOfDimension_iff_of_topologicalKrullDim_le hX).mp hx).1

variable [IsNoetherian X]

/-- On a Noetherian scheme of dimension at most `n`, the Chow group `CH_n(X)` is a finitely
generated abelian group. -/
lemma ChowGroup.finite_of_topologicalKrullDim_le (hX : topologicalKrullDim X ≤ n) :
    Module.Finite ℤ (ChowGroup X n) :=
  have := (finite_pointsOfDimension_of_topologicalKrullDim_le hX).to_subtype
  .of_basis (ChowGroup.basisOfTopologicalKrullDimLE hX)

/-- On a Noetherian scheme of dimension at most `n`, the rank of the Chow group `CH_n(X)` is the
number of points of dimension `n`, that is, of irreducible components of dimension `n`. -/
lemma ChowGroup.finrank_eq_ncard_of_topologicalKrullDim_le (hX : topologicalKrullDim X ≤ n) :
    Module.finrank ℤ (ChowGroup X n) = (pointsOfDimension X n).ncard := by
  rw [Module.finrank_eq_nat_card_basis (ChowGroup.basisOfTopologicalKrullDimLE hX),
    Nat.card_coe_set_eq]

end Noetherian

end TauCeti.AlgebraicGeometry.Chow
