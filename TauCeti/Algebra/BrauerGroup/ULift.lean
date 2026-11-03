/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.BaseChange
public import Mathlib.Algebra.Field.ULift
import TauCeti.Algebra.BrauerGroup.Splitting
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# The Brauer group of a universe lift

For a field `K : Type u`, the lift `ULift.{w} K` is a field in the larger universe `max u w`, and
its Brauer group is formed from central simple algebras in that larger universe. This file
identifies it with the Brauer group of `K`:

`TauCeti.BrauerGroup.uliftEquiv K : BrauerGroup K ≃* BrauerGroup (ULift.{w} K)`.

The map is scalar extension `A ↦ ULift K ⊗[K] A` along the field isomorphism `K → ULift K`
(`TauCeti.BrauerGroup.uliftEquiv_mk`). The same-universe homomorphism
`TauCeti.BrauerGroup.baseChange` cannot be used, because it binds both fields to one universe so
that the base field can serve as the identity class; here the tensor product lands in the universe
of `ULift K`, which is where its Brauer group lives.

Injectivity is the splitting criterion: an algebra split by `ULift K` is a matrix algebra over
`ULift K`, hence over `K`. Surjectivity needs a model of a central simple `ULift K`-algebra `B` in
the smaller universe: `B` regarded as a `K`-algebra is finite-dimensional over `K`, hence small,
and its shrinking `Shrink.{u} B` is a central simple `K`-algebra whose scalar extension is `B`
again.

The universe lift is an actual field in a larger universe, not a field postulated to be
equivalent to one in a smaller universe, so no smallness hypothesis on `K` is involved.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §2.4.
-/

public section

noncomputable section

universe u w

namespace TauCeti

open scoped TensorProduct

namespace BrauerGroup

variable (K : Type u) [Field K]

/-- Scalar extension of Brauer classes along `K → ULift K`, landing in the Brauer group formed in
the universe of `ULift K`. It is bundled as `TauCeti.BrauerGroup.uliftEquiv`. -/
private def ulift : BrauerGroup.{u, u} K →* BrauerGroup.{max u w, max u w} (ULift.{w} K) where
  toFun x := Quotient.liftOn x (fun A ↦ mk (CSA.baseChange (ULift.{w} K) A))
    fun _ _ h ↦ Quotient.sound (isBrauerEquivalent_baseChange_congr _ h)
  map_one' := mk_eq_mk_of_algEquiv (Algebra.TensorProduct.rid K (ULift.{w} K) (ULift.{w} K))
  map_mul' x y := Quotient.inductionOn₂ x y fun A B ↦
    mk_eq_mk_of_algEquiv (Algebra.TensorProduct.baseChangeTensorAlgEquiv K (ULift.{w} K) A B)

private theorem ulift_mk (A : CSA.{u, u} K) :
    ulift.{u, w} K (mk A) = mk (CSA.baseChange (ULift.{w} K) A) :=
  (rfl)

/-- A central simple `K`-algebra split by `ULift K` is split by `K`. -/
private theorem ulift_injective : Function.Injective (ulift.{u, w} K) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  induction x using BrauerGroup.inductionOn with
  | h A =>
  rw [ulift_mk, mk_eq_one_iff, isBrauerTrivial_iff_isSplittingField,
    Algebra.isSplittingField_self_iff] at hx
  obtain ⟨n, ⟨e⟩⟩ := hx
  refine mk_eq_one_iff.2 (isBrauerTrivial_of_isSplittingField K
    ((Algebra.isSplittingField_self_iff K A).2 ⟨n, ⟨?_⟩⟩))
  exact (Algebra.TensorProduct.lid K A).symm.trans
    ((Algebra.TensorProduct.congr (ULift.algEquiv (R := K) (A := K)).symm AlgEquiv.refl).trans
      ((e.restrictScalars K).trans (ULift.algEquiv (R := K) (A := K)).mapMatrix))

/-- Every central simple `ULift K`-algebra `B` is the scalar extension of `Shrink.{u} B`, where
`B` is regarded as a `K`-algebra. -/
private theorem ulift_surjective : Function.Surjective (ulift.{u, w} K) := by
  intro x
  induction x using BrauerGroup.inductionOn with
  | h B =>
  let : Algebra K B := Algebra.restrictScalars K (ULift.{w} K) B
  have : IsScalarTower K (ULift.{w} K) B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional K B := Module.Finite.trans (ULift.{w} K) B
  have : Algebra.IsCentral K B := ⟨fun z hz ↦ by
    obtain ⟨c, rfl⟩ := (Algebra.IsCentral.mem_center_iff (ULift.{w} K)).1 hz
    exact ⟨c.down, rfl⟩⟩
  have : Small.{u} B := Module.Finite.small K B
  -- `Algebra.IsCentral.of_algEquiv` needs both algebras in one universe, and `Shrink.{u} B` is
  -- in a smaller universe than `B`, so centrality is transported by hand.
  have : Algebra.IsCentral K (Shrink.{u} B) := ⟨fun z hz ↦ by
    obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff K).1
      ((MulEquivClass.apply_mem_center_iff (Shrink.algEquiv K B)).2 hz)
    exact ⟨c, (Shrink.algEquiv K B).injective (by simpa using hc.symm)⟩⟩
  have : IsSimpleRing (Shrink.{u} B) :=
    IsSimpleRing.of_ringEquiv (Shrink.algEquiv K B).symm.toRingEquiv inferInstance
  refine ⟨mk (CSA.of K (Shrink.{u} B)), ?_⟩
  rw [ulift_mk]
  refine mk_eq_mk_of_algEquiv (AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.congr (ULift.algEquiv (R := K) (A := K))
      (Shrink.algEquiv K B)).trans (Algebra.TensorProduct.lid K B)).toRingEquiv) fun c ↦ ?_)
  simp [Algebra.smul_def, IsScalarTower.algebraMap_apply K (ULift.{w} K) B, ULift.ext_iff]

/-- **The Brauer group of a universe lift**: scalar extension along the field isomorphism
`K → ULift K` identifies the Brauer group of `K : Type u` with the Brauer group of
`ULift.{w} K`, formed from central simple algebras in the universe `max u w`. -/
def uliftEquiv : BrauerGroup.{u, u} K ≃* BrauerGroup.{max u w, max u w} (ULift.{w} K) :=
  MulEquiv.ofBijective (ulift.{u, w} K) ⟨ulift_injective K, ulift_surjective K⟩

/-- `TauCeti.BrauerGroup.uliftEquiv` sends the class of `A` to the class of its scalar extension
`ULift K ⊗[K] A`. -/
@[simp]
theorem uliftEquiv_mk (A : CSA.{u, u} K) :
    uliftEquiv.{u, w} K (mk A) = mk (CSA.baseChange (ULift.{w} K) A) :=
  (rfl)

end BrauerGroup

end TauCeti
