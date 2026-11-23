/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.BaseChange
-- Non-public: the semisimplicity of base change for modules over an algebra, and the action of
-- `L ⊗[k] B` on `L ⊗[k] V`, are used only inside the proof.
import TauCeti.Algebra.TensorProduct.Module
import TauCeti.RingTheory.Semisimple.BaseChange

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

/-- The `L`-algebra map `L[G] → L ⊗[k] B` sending `g` to `1 ⊗ ψ g`, for a `k`-algebra map
`ψ : k[G] → B`. -/
private noncomputable abbrev liftBaseChange {B : Type*} [Ring B] [Algebra k B]
    (ψ : k[G] →ₐ[k] B) : L[G] →ₐ[L] L ⊗[k] B :=
  MonoidAlgebra.lift L _ G ((Algebra.TensorProduct.includeRight : B →ₐ[k] L ⊗[k] B).toMonoidHom.comp
    (ψ.toMonoidHom.comp (MonoidAlgebra.of k G)))

/-- `L[G] → L ⊗[k] B` is surjective when `ψ : k[G] → B` is. -/
private theorem liftBaseChange_surjective {B : Type*} [Ring B] [Algebra k B] (ψ : k[G] →ₐ[k] B)
    (hψ : Function.Surjective ψ) : Function.Surjective (liftBaseChange L ψ) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | tmul l b =>
    obtain ⟨a, rfl⟩ := hψ b
    induction a using MonoidAlgebra.induction_on generalizing l with
    | of g => exact ⟨l • MonoidAlgebra.of L G g, by simp [TensorProduct.smul_tmul']⟩
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha l
      obtain ⟨y, hy⟩ := hb l
      exact ⟨x + y, by rw [map_add, hx, hy, map_add, TensorProduct.tmul_add]⟩
    | smul c a ha =>
      obtain ⟨x, hx⟩ := ha (c • l)
      exact ⟨x, by rw [hx, map_smul, TensorProduct.smul_tmul]⟩

/-- `r ∈ L[G]` acts on `L ⊗[k] V` through `L ⊗[k] B`, for `B` the image of `k[G]` in `End_k(V)`,
as it does through the base-changed representation. -/
private theorem tensorPairAction_liftBaseChange_apply (ρ : Representation k G V) (r : L[G])
    (x : L ⊗[k] V) :
    TauCeti.BialgebraModule.tensorPairAction k L V (A := L) (B := ρ.asAlgebraHom.range)
      (liftBaseChange L ρ.asAlgebraHom.rangeRestrict r) x =
      (ρ.baseChange L).asAlgebraHom r x := by
  set act := TauCeti.BialgebraModule.tensorPairAction k L V (A := L) (B := ρ.asAlgebraHom.range)
  have hscalar (c : L) (x : L ⊗[k] V) : act (c ⊗ₜ 1) x = c • x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | tmul l v => simp [act, TensorProduct.smul_tmul']
  induction r using MonoidAlgebra.induction_on generalizing x with
  | of g =>
    rw [asAlgebraHom_of]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul l v =>
      simp only [act, MonoidAlgebra.lift_of]
      simp [Subalgebra.smul_def]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul c a ha =>
    rw [map_smul (liftBaseChange L _) c a, Algebra.smul_def c, map_mul act, mul_apply_eq_comp, ha,
      map_smul (ρ.baseChange L).asAlgebraHom c a, LinearMap.smul_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact hscalar c _

/-- **Semisimplicity is preserved by base change over a perfect field.** A finite-dimensional
semisimple representation of a monoid over a perfect field `k` remains semisimple after extending
scalars to any field extension `L / k`. -/
instance isSemisimpleRepresentation_baseChange [PerfectField k] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsSemisimpleRepresentation] :
    (ρ.baseChange L).IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at *
  set ψ := ρ.asAlgebraHom.rangeRestrict
  let : Module ρ.asAlgebraHom.range ρ.asModule := (inferInstance : Module ρ.asAlgebraHom.range V)
  have : RingHomSurjective ψ.toRingHom := ⟨AlgHom.rangeRestrict_surjective _⟩
  have : IsSemisimpleModule ρ.asAlgebraHom.range V :=
    (LinearMap.isSemisimpleModule_iff_of_bijective (M' := ρ.asModule) (N' := ρ.asModule)
      (σ := ψ.toRingHom) ⟨⟨id, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ Function.bijective_id).mp ‹_›
  let act := TauCeti.BialgebraModule.tensorPairAction k L V (A := L) (B := ρ.asAlgebraHom.range)
  let : Module (L ⊗[k] ρ.asAlgebraHom.range) (L ⊗[k] V) := Module.compHom _ act.toRingHom
  have hss := TauCeti.isSemisimpleModule_tensorProduct_of_perfectField (k := k)
    (A := ρ.asAlgebraHom.range) (M := V) L fun l l' a m ↦ by
      -- The action on `L ⊗[k] V` is `act` through `Module.compHom`.
      change act (l ⊗ₜ a) (l' ⊗ₜ m) = _
      simp [act]
  let : Module (L ⊗[k] ρ.asAlgebraHom.range) (ρ.baseChange L).asModule :=
    (inferInstance : Module (L ⊗[k] ρ.asAlgebraHom.range) (L ⊗[k] V))
  have : RingHomSurjective (liftBaseChange L ψ).toRingHom :=
    ⟨liftBaseChange_surjective L ψ (AlgHom.rangeRestrict_surjective _)⟩
  exact (LinearMap.isSemisimpleModule_iff_of_bijective (M' := (ρ.baseChange L).asModule)
    (N' := (ρ.baseChange L).asModule) (σ := (liftBaseChange L ψ).toRingHom)
    ⟨⟨id, fun _ _ ↦ rfl⟩, fun r x ↦ by exact (tensorPairAction_liftBaseChange_apply L ρ r x).symm⟩
    Function.bijective_id).mpr hss

end Representation
