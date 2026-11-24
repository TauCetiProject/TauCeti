/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
-- Non-public: used only inside proofs. The Wedderburn–Artin presentation, the matrix and product
-- comparisons for tensor products, the simplicity of a tensor product with a central simple
-- algebra, the reducedness of a separable base change and the canonical action of
-- `L ⊗[k] B` on `L ⊗[k] M` are the steps of the arguments below.
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.TensorProduct.Pi
import TauCeti.Algebra.CentralSimple.TensorProduct
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.Algebra.TensorProduct.Module
import TauCeti.RingTheory.SimpleModule.Basic
import TauCeti.RingTheory.Unramified.Field

/-!
# Semisimplicity is preserved by base change over a perfect field

Let `k` be a perfect field and `L / k` any field extension. A finite-dimensional semisimple
`k`-algebra `B` has semisimple base change `L ⊗[k] B`, and a finite-dimensional semisimple module
`M` over a `k`-algebra `A` has semisimple base change `L ⊗[k] M` over `L ⊗[k] A`.

The proof for algebras follows the structure of `B`. By Wedderburn–Artin, `B` is a finite product
of matrix algebras `Mₙ(D)` over division algebras `D` finite-dimensional over `k`, and base change
commutes with finite products and matrix algebras, so it suffices to treat `L ⊗[k] D`. The centre
`Z` of `D` is a finite field extension of `k`, separable because `k` is perfect, and `D` is central
simple over `Z`. Then `L ⊗[k] D = D ⊗[Z] (Z ⊗[k] L)`, and `Z ⊗[k] L` is a reduced Artinian ring
(a separable base change is reduced), hence a finite product of fields `F`. Each `D ⊗[Z] F` is
simple, as the tensor product of a central simple algebra with a simple one, and Artinian, so
`L ⊗[k] D` is a finite product of simple Artinian rings.

For modules, the action of `A` on `M` factors through its image `B` in `End_k(M)`, a
finite-dimensional semisimple algebra (`TauCeti.isSemisimpleRing_range_lsmul`, in
`TauCeti.RingTheory.SimpleModule.Basic`), and the action of
`L ⊗[k] A` on `L ⊗[k] M` factors through the semisimple ring `L ⊗[k] B`.

Perfectness is essential. For `k = 𝔽_p(s)` and `B = k(s^{1/p})`, the field `B` is semisimple, but
`B ⊗[k] B` contains the nonzero nilpotent `s^{1/p} ⊗ 1 - 1 ⊗ s^{1/p}`, so it is not semisimple.
Finite-dimensionality is essential too: for `B = k(t)`, the ring `k(t) ⊗[k] k(t)` is a domain that
is not a field, so it is not semisimple.

## Main results

* `TauCeti.isSemisimpleRing_tensorProduct_of_perfectField`: **base change of a finite-dimensional
  semisimple algebra over a perfect field is semisimple** (an instance).
* `TauCeti.isSemisimpleModule_tensorProduct_of_perfectField`: **base change of a
  finite-dimensional semisimple module over a perfect field is semisimple**, over the base change
  of the algebra.
* `TauCeti.isSemisimpleRing_tensorProduct_of_isCentral`: `D ⊗[Z] R` is semisimple for `D` finite
  central simple over a field `Z` and `R` a reduced commutative Artinian `Z`-algebra.

## References

* Stacks Project, tag 030U (separable base change is reduced; here the instance
  `TauCeti.Algebra.FormallyUnramified.isReduced_tensorProduct_field`) and tag 074H (base
  change of a central simple algebra).
* N. Bourbaki, *Algebra, Chapter 8*, §12, no. 7, for the behaviour of semisimplicity under
  extension of scalars.
-/

public section

open scoped TensorProduct

namespace TauCeti


/-! ### Base change of a central simple algebra to a reduced Artinian ring -/

/-- **A central simple algebra tensored with a reduced Artinian ring is semisimple.** For `D`
finite-dimensional central simple over a field `Z` and `R` a reduced commutative Artinian
`Z`-algebra, `R` is a finite product of fields `F`, so `D ⊗[Z] R` is the product of the simple
Artinian rings `D ⊗[Z] F`. -/
theorem isSemisimpleRing_tensorProduct_of_isCentral {Z D R : Type*} [Field Z] [Ring D]
    [Algebra Z D] [Algebra.IsCentral Z D] [IsSimpleRing D] [FiniteDimensional Z D] [CommRing R]
    [Algebra Z R] [IsArtinianRing R] [IsReduced R] : IsSemisimpleRing (D ⊗[Z] R) := by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have (m : MaximalSpectrum R) : IsSemisimpleRing (D ⊗[Z] (R ⧸ m.asIdeal)) := by
    let : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field _
    have : IsArtinianRing (D ⊗[Z] (R ⧸ m.asIdeal)) :=
      have : IsArtinianRing ((R ⧸ m.asIdeal) ⊗[Z] D) := .of_finite (R ⧸ m.asIdeal) _
      (Algebra.TensorProduct.comm Z (R ⧸ m.asIdeal) D).toRingEquiv.isArtinianRing
    infer_instance
  exact ((Algebra.TensorProduct.congr AlgEquiv.refl
    ((IsArtinianRing.equivPi R).restrictScalars Z)).trans
      (Algebra.TensorProduct.piRight Z Z D _)).symm.toRingEquiv.isSemisimpleRing

/-! ### Base change over a perfect field -/

section PerfectField

variable {k : Type*} [Field k] [PerfectField k] (L : Type*) [Field L] [Algebra k L]

/-- The base change of a finite-dimensional division algebra over a perfect field is semisimple:
it is `D ⊗[Z] (Z ⊗[k] L)` for the centre `Z` of `D`, and `Z ⊗[k] L` is reduced since `Z / k` is
separable. -/
private theorem isSemisimpleRing_tensorProduct_divisionRing (D : Type*) [DivisionRing D]
    [Algebra k D] [FiniteDimensional k D] : IsSemisimpleRing (L ⊗[k] D) := by
  let : Field (Subalgebra.center k D) := inferInstanceAs (Field (Subring.center D))
  have : FiniteDimensional (Subalgebra.center k D) D := Subalgebra.finite_centerAlgebra_of_finite
  have : Algebra.IsSeparable k (Subalgebra.center k D) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified k (Subalgebra.center k D) :=
    Algebra.FormallyUnramified.of_isSeparable k _
  have := isSemisimpleRing_tensorProduct_of_isCentral (Z := Subalgebra.center k D) (D := D)
    (R := Subalgebra.center k D ⊗[k] L)
  have : IsSemisimpleRing (D ⊗[k] L) :=
    ((Algebra.TensorProduct.assoc k (Subalgebra.center k D) (Subalgebra.center k D) D
      (Subalgebra.center k D) L).symm.toRingEquiv.trans
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid (Subalgebra.center k D)
        (Subalgebra.center k D) D)
        AlgEquiv.refl).toRingEquiv).isSemisimpleRing
  exact (Algebra.TensorProduct.comm k D L).toRingEquiv.isSemisimpleRing

/-- **Base change of a finite-dimensional semisimple algebra over a perfect field is
semisimple.** For a perfect field `k`, a finite-dimensional semisimple `k`-algebra `B` and any
field extension `L / k`, the ring `L ⊗[k] B` is semisimple.

Both hypotheses on `B` and `k` are needed: see the module docstring. In characteristic zero every
field is perfect, so this applies to every field extension of characteristic zero. -/
instance isSemisimpleRing_tensorProduct_of_perfectField (B : Type*) [Ring B] [Algebra k B]
    [FiniteDimensional k B] [IsSemisimpleRing B] : IsSemisimpleRing (L ⊗[k] B) := by
  obtain ⟨n, D, d, _, _, _, -, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite k B
  have (i : Fin n) : IsSemisimpleRing (L ⊗[k] Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
    have := isSemisimpleRing_tensorProduct_divisionRing (k := k) L (D i)
    exact ((Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor (Fin (d i)) k (D i))).trans
      ((Algebra.TensorProduct.assoc k k k L (D i) (Matrix (Fin (d i)) (Fin (d i)) k)).symm.trans
        (matrixEquivTensor (Fin (d i)) k (L ⊗[k] D i)).symm)).symm.toRingEquiv.isSemisimpleRing
  exact ((Algebra.TensorProduct.congr AlgEquiv.refl e).trans
    (Algebra.TensorProduct.piRight k k L _)).symm.toRingEquiv.isSemisimpleRing

variable {A M : Type*} [Ring A] [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]

/-- **Base change of a finite-dimensional semisimple module over a perfect field is semisimple.**
Let `k` be a perfect field, `A` a `k`-algebra and `M` an `A`-module that is semisimple and
finite-dimensional over `k`. For every field extension `L / k`, the base change `L ⊗[k] M` is a
semisimple module over `L ⊗[k] A`, for any action of `L ⊗[k] A` on `L ⊗[k] M` given on pure
tensors by `(l ⊗ a) • (l' ⊗ m) = (l * l') ⊗ (a • m)`, such as the one obtained from
`TauCeti.BialgebraModule.tensorPairAction` by `Module.compHom`.

The action of `A` factors through its image `B` in `End_k(M)`, which is a finite-dimensional
semisimple algebra, so the action of `L ⊗[k] A` factors through the semisimple ring
`L ⊗[k] B`. -/
theorem isSemisimpleModule_tensorProduct_of_perfectField [FiniteDimensional k M]
    [IsSemisimpleModule A M] [Module (L ⊗[k] A) (L ⊗[k] M)]
    (h : ∀ (l l' : L) (a : A) (m : M), (l ⊗ₜ[k] a) • (l' ⊗ₜ[k] m) = (l * l') ⊗ₜ[k] (a • m)) :
    IsSemisimpleModule (L ⊗[k] A) (L ⊗[k] M) := by
  have := isSemisimpleRing_range_lsmul (k := k) (A := A) (M := M)
  let : Module (L ⊗[k] (Algebra.lsmul k (A := A) k M).range) (L ⊗[k] M) :=
    Module.compHom _ (BialgebraModule.tensorPairAction k L M).toRingHom
  let φ := (Algebra.TensorProduct.map (AlgHom.id k L)
    (Algebra.lsmul k (A := A) k M).rangeRestrict).toRingHom
  refine (RingHom.isSemisimpleModule_iff_of_surjective (M := L ⊗[k] M) φ
    (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id
      (AlgHom.rangeRestrict_surjective _)) fun t x ↦ ?_).mpr inferInstance
  -- Both actions are pulled back along ring maps (`Module.compHom`), so `•` unfolds to them.
  change φ t • x = t • x
  symm
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, add_smul, ht, hu]
  | tmul l a =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul l' m =>
      -- The action of `L ⊗[k] range` on `L ⊗[k] M` is `tensorPairAction` through `Module.compHom`.
      change _ = BialgebraModule.tensorPairAction k L M (Algebra.TensorProduct.map _ _ (l ⊗ₜ a))
        (l' ⊗ₜ m)
      simp [h, Subalgebra.smul_def]

end PerfectField

end TauCeti
