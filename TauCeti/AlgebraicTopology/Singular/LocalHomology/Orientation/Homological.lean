/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Transport

/-!
# Homological orientations of manifolds

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space `E`, that is, a
topological manifold without boundary. A *homological orientation* of `M` in degree `d`
(`TauCeti.HomologicalOrientation M E d`) is a choice of local orientation, a generator of the
integral local homology `H_d(M, M ∖ {x}; ℤ)`, at every point `x` of `M`, which is carried to itself
by the transport of local homology along paths. In the dimension `d = finrank ℝ E` of the
manifold, this is Hatcher's orientation of `M`: transport is computed through balls in charts
(`TauCeti.localHomologyRestriction_comp_localHomologyTransport`), so invariance under transport is
his local consistency condition. In other degrees the local homology vanishes, so the structure is
only of interest in the dimension of the manifold, where every statement below assumes it.

Orientations are the input of the integral fundamental class of a compact manifold
(`TauCeti.HomologicalOrientation.fundamentalClass`).

On a connected manifold an orientation is determined by its value at a single point
(`TauCeti.HomologicalOrientation.eq_of_apply_eq`), so a connected manifold has either no
orientation or exactly the two orientations `o` and `-o`
(`TauCeti.HomologicalOrientation.eq_or_eq_neg`, `TauCeti.HomologicalOrientation.neg_ne`). A
simply connected manifold is orientable: a local orientation at one point extends uniquely to an
orientation (`TauCeti.HomologicalOrientation.ofSimplyConnectedSpace`).

## Main definitions

* `TauCeti.HomologicalOrientation M E d`: a transport-invariant family of local orientations.
* `-o`: the reversed orientation.
* `TauCeti.HomologicalOrientation.ofSimplyConnectedSpace`: the orientation of a simply connected
  manifold extending a given local orientation.

## Main results

* `TauCeti.HomologicalOrientation.eq_of_apply_eq`: on a connected manifold, two orientations
  agreeing at one point are equal.
* `TauCeti.HomologicalOrientation.eq_or_eq_neg`: on a connected manifold, any two orientations
  agree up to reversal.
* `TauCeti.HomologicalOrientation.neg_ne`: on a nonempty manifold, an orientation differs from its
  reversal.
* `TauCeti.HomologicalOrientation.nonempty_of_simplyConnectedSpace`: a simply connected manifold
  has an orientation.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti

variable (M E : Type w) [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  (d : ℕ)

/-- A homological orientation of `M` in degree `d`: a local orientation at every point, that is a
generator of the integral local homology `H_d(M, M ∖ {x}; ℤ)`, such that transport along every path
class carries the local orientation at its start to the local orientation at its end. In the
dimension of `M` this is an orientation of the manifold `M` in the sense of Hatcher. -/
structure HomologicalOrientation where
  /-- The local orientation at each point. -/
  toFun (x : M) : LocalOrientation M x d
  /-- Transport along a path class carries the local orientation at its start to the local
  orientation at its end. -/
  localOrientationTransport_toFun' {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localOrientationTransport M E d f (toFun x.as) = toFun y.as

namespace HomologicalOrientation

variable {M E d}

instance : DFunLike (HomologicalOrientation M E d) M (fun x ↦ LocalOrientation M x d) where
  coe := toFun
  coe_injective o o' h := by
    cases o
    cases o'
    congr

@[simp]
theorem toFun_eq_coe (o : HomologicalOrientation M E d) : o.toFun = o :=
  (rfl)

@[simp]
theorem coe_mk (o : ∀ x : M, LocalOrientation M x d)
    (h : ∀ {x y : FundamentalGroupoid M} (f : x ⟶ y),
      localOrientationTransport M E d f (o x.as) = o y.as) :
    ⇑(⟨o, h⟩ : HomologicalOrientation M E d) = o :=
  (rfl)

@[ext]
theorem ext {o o' : HomologicalOrientation M E d} (h : ∀ x, o x = o' x) : o = o' :=
  DFunLike.ext _ _ h

/-- Transport along a path class carries the local orientation at its start to the local
orientation at its end. -/
@[simp]
theorem localOrientationTransport_apply (o : HomologicalOrientation M E d)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localOrientationTransport M E d f (o x.as) = o y.as :=
  o.localOrientationTransport_toFun' f

/-- The reversed orientation, reversing the local orientation at every point. -/
instance : InvolutiveNeg (HomologicalOrientation M E d) where
  neg o := ⟨fun x ↦ -o x, fun f ↦ by
    rw [localOrientationTransport_neg, localOrientationTransport_apply]⟩
  neg_neg o := ext fun x ↦ neg_neg (o x)

@[simp]
theorem neg_apply (o : HomologicalOrientation M E d) (x : M) : (-o) x = -o x :=
  (rfl)

/-- **An orientation of a connected manifold is determined by its value at one point.** -/
theorem eq_of_apply_eq [ConnectedSpace M] {o o' : HomologicalOrientation M E d} {x : M}
    (h : o x = o' x) : o = o' := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  refine ext fun y ↦ ?_
  -- Transport the agreement at `x` along a path from `x` to `y`.
  let f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y)
  have hf := congrArg (localOrientationTransport M E d f) h
  rwa [localOrientationTransport_apply, localOrientationTransport_apply] at hf

/-- **A connected manifold has at most two orientations**: in the dimension of the manifold, any
two orientations of a connected manifold agree up to reversal. -/
theorem eq_or_eq_neg [ConnectedSpace M] (hd : finrank ℝ E = d)
    (o o' : HomologicalOrientation M E d) : o' = o ∨ o' = -o := by
  subst hd
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  rcases IsLocalOrientation.eq_or_eq_neg
      (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))
      (o x).property (o' x).property with h | h
  · exact Or.inl (eq_of_apply_eq (x := x) (Subtype.ext h))
  · exact Or.inr (eq_of_apply_eq (x := x) (Subtype.ext h))

/-- In the dimension of a nonempty manifold, an orientation differs from its reversal. -/
theorem neg_ne [Nonempty M] (hd : finrank ℝ E = d) (o : HomologicalOrientation M E d) :
    -o ≠ o := by
  subst hd
  obtain ⟨x⟩ := ‹Nonempty M›
  intro h
  exact IsLocalOrientation.neg_ne
    (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))
    (o x).property (congrArg Subtype.val (DFunLike.congr_fun h x))

section SimplyConnected

variable [SimplyConnectedSpace M]

/-- **Orientations of a simply connected manifold.** A local orientation at one point extends, by
transport along paths, to an orientation; all paths between two points are homotopic, so the
transport does not depend on the path. -/
def ofSimplyConnectedSpace (x : M) (z : LocalOrientation M x d) : HomologicalOrientation M E d where
  toFun y := localOrientationTransport M E d
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y) :
      FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) z
  localOrientationTransport_toFun' f := by
    rw [← Equiv.trans_apply, ← localOrientationTransport_comp]
    exact congrArg (localOrientationTransport M E d · z)
      (Subsingleton.elim (α := Path.Homotopic.Quotient x _) _ _)

/-- The orientation extending a local orientation `z` at `x` is, at `y`, the transport of `z`
along any path from `x` to `y`. -/
theorem ofSimplyConnectedSpace_apply (x : M) (z : LocalOrientation M x d) (y : M)
    (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ofSimplyConnectedSpace (E := E) x z y = localOrientationTransport M E d f z :=
  congrArg (localOrientationTransport M E d · z)
    (Subsingleton.elim (α := Path.Homotopic.Quotient x y) _ _)

/-- The orientation extending a local orientation `z` at `x` is `z` at `x`. -/
@[simp]
theorem ofSimplyConnectedSpace_apply_self (x : M) (z : LocalOrientation M x d) :
    ofSimplyConnectedSpace (E := E) x z x = z := by
  rw [ofSimplyConnectedSpace_apply x z x (𝟙 _), localOrientationTransport_id, Equiv.refl_apply]

/-- A simply connected manifold is orientable. -/
theorem nonempty_of_simplyConnectedSpace (hd : finrank ℝ E = d) :
    Nonempty (HomologicalOrientation M E d) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  cases d with
  | zero => exact ⟨ofSimplyConnectedSpace x (exists_localOrientation_of_zero_dim_chart x hd).some⟩
  | succ d => exact ⟨ofSimplyConnectedSpace x (exists_localOrientation_of_chart x hd).some⟩

end SimplyConnected

end HomologicalOrientation

end TauCeti
