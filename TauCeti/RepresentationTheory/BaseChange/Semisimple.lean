/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.BaseChange
-- Non-public: the semisimplicity of base change for modules over an algebra, and the action of
-- `L ⊗[k] B` on `L ⊗[k] V`, are used only inside the proof.
import TauCeti.Algebra.TensorProduct.Module
import TauCeti.RepresentationTheory.Semisimple.Range
import TauCeti.RingTheory.TensorProduct.MonoidAlgebra
import TauCeti.RingTheory.Semisimple.BaseChange
import TauCeti.RingTheory.SimpleModule.Basic

/-!
# Semisimple representations stay semisimple under base change over a perfect field

Let `k` be a perfect field and `ρ` a finite-dimensional semisimple representation of a monoid `G`
over `k`. Then for every field extension `L / k` the base change `L ⊗[k] ρ` is semisimple
(`Representation.isSemisimpleRepresentation_baseChange`). The continuous version is in
`TauCeti.RepresentationTheory.Continuous.BaseChangeSemisimple`.

The proof applies `TauCeti.isSemisimpleModule_tensorProduct_of_perfectField` to the image `B` of
`k[G]` in `End_k(V)`, with `V` as a `B`-module: `L ⊗[k] V` is a semisimple module over `L ⊗[k] B`,
and `L[G]` acts on it through a surjection onto `L ⊗[k] B`.

This fails for imperfect `k`: for `k = 𝔽_p(s)`, `L = k(s^{1/p})` and `G = Lˣ` acting on `V = L`
by multiplication, `V` is simple, but `L ⊗[k] V` is the regular module of the non-reduced ring
`L ⊗[k] L`, which is not semisimple.
-/

public section

open scoped TensorProduct MonoidAlgebra

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (L : Type*) [Field L] [Algebra k L]

/-- The `k`-algebra map `L[G] → L ⊗[k] B` sending `c • g` to `c ⊗ ψ g`, for a `k`-algebra map
`ψ : k[G] → B`: the identification `L[G] ≃ k[G] ⊗[k] L ≃ L ⊗[k] k[G]` followed by the tensor map
of `ψ`. -/
private noncomputable abbrev liftBaseChange {B : Type*} [Ring B] [Algebra k B]
    (ψ : k[G] →ₐ[k] B) : L[G] →ₐ[k] L ⊗[k] B :=
  (Algebra.TensorProduct.map (AlgHom.id k L) ψ).comp
    ((Algebra.TensorProduct.comm k k[G] L).toAlgHom.comp
      (MonoidAlgebra.tensorAlgEquiv k L G).symm.toAlgHom)

/-- `r ∈ L[G]` acts on `L ⊗[k] V` through `L ⊗[k] B`, for `B` the image of `k[G]` in `End_k(V)`,
as it does through the base-changed representation. -/
private theorem tensorPairAction_liftBaseChange_apply (ρ : Representation k G V) (r : L[G])
    (x : L ⊗[k] V) :
    TauCeti.BialgebraModule.tensorPairAction k L V (A := L) (B := ρ.asAlgebraHom.range)
      (liftBaseChange L ρ.asAlgebraHom.rangeRestrict r) x =
      (ρ.baseChange L).asAlgebraHom r x := by
  induction r using MonoidAlgebra.induction_linear generalizing x with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g c =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul l v => simp [Subalgebra.smul_def, TensorProduct.smul_tmul']

/-- **Semisimplicity is preserved by base change over a perfect field.** A finite-dimensional
semisimple representation of a monoid over a perfect field `k` remains semisimple after extending
scalars to any field extension `L / k`. -/
instance isSemisimpleRepresentation_baseChange [PerfectField k] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsSemisimpleRepresentation] :
    (ρ.baseChange L).IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  set ψ := ρ.asAlgebraHom.rangeRestrict
  have := ρ.isSemisimpleModule_range_asAlgebraHom
  let act := TauCeti.BialgebraModule.tensorPairAction k L V (A := L) (B := ρ.asAlgebraHom.range)
  let : Module (L ⊗[k] ρ.asAlgebraHom.range) (L ⊗[k] V) := Module.compHom _ act.toRingHom
  have hss := TauCeti.isSemisimpleModule_tensorProduct_of_perfectField (k := k)
    (A := ρ.asAlgebraHom.range) (M := V) L fun l l' a m ↦ by
      -- The action on `L ⊗[k] V` is `act` through `Module.compHom`.
      change act (l ⊗ₜ a) (l' ⊗ₜ m) = _
      simp [act]
  let : Module (L ⊗[k] ρ.asAlgebraHom.range) (ρ.baseChange L).asModule :=
    (inferInstance : Module (L ⊗[k] ρ.asAlgebraHom.range) (L ⊗[k] V))
  exact (RingHom.isSemisimpleModule_iff_of_surjective (M := (ρ.baseChange L).asModule)
    (liftBaseChange L ψ).toRingHom
    ((Algebra.TensorProduct.map_surjective _ _ Function.surjective_id
      (AlgHom.rangeRestrict_surjective _)).comp
        ((Algebra.TensorProduct.comm k k[G] L).surjective.comp
          (MonoidAlgebra.tensorAlgEquiv k L G).symm.surjective))
    fun r x ↦ tensorPairAction_liftBaseChange_apply L ρ r x).mpr hss

end Representation
