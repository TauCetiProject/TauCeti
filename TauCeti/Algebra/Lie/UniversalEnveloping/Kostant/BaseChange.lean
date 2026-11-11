/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.HopfAlgebra
public import TauCeti.Algebra.Coalgebra.BaseChange
public import TauCeti.Algebra.HopfAlgebra.BaseChange
public import TauCeti.RingTheory.Subring.RationalBaseChange

/-!
# The Kostant form is an integral Hopf form of the enveloping algebra

Let `L` be a Lie algebra over `ℚ` and let `e : ι → L` and `h : κ → L` be the two distinguished
families out of which `TauCeti.UniversalEnvelopingAlgebra.kostantForm` is built. As soon as those
families generate `L` as a Lie algebra, the resulting subring is an integral form of the whole
enveloping algebra: extending its scalars to `ℚ` recovers `U(L)`,

```text
ℚ ⊗[ℤ] kostantForm e h ≃ₐc[ℚ] UniversalEnvelopingAlgebra ℚ L.
```

The spanning half of that statement is
`TauCeti.UniversalEnvelopingAlgebra.span_kostantForm_eq_top`, proved with the form itself. What
this file adds is that the comparison map is an isomorphism and not merely a surjection: it is
`Subring.ratBaseChangeEquiv` applied to the form, upgraded to a bialgebra equivalence using the
integral coproduct and counit. The map out of `ℚ ⊗[ℤ] R` is injective for every subring `R` of a
`ℚ`-algebra, so a rationally spanning subring is automatically a `ℤ`-form. The comparison also
preserves the antipode, as every bialgebra homomorphism between Hopf algebras does.

Nothing here bounds the form from the other side. That the form is a *free* `ℤ`-module on the
ordered monomials in divided powers, the integral Poincaré--Birkhoff--Witt theorem, is a separate
statement and is not proved here. The results below identify the rational Hopf algebra obtained
from the form and allow denominators to be cleared.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.kostantFormBaseChange`: the isomorphism
  `ℚ ⊗[ℤ] kostantForm e h ≃ₐc[ℚ] UniversalEnvelopingAlgebra ℚ L`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exists_natCast_smul_mem_kostantForm`: every element of the
  enveloping algebra is carried into the form by a nonzero natural number.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open scoped TensorProduct

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

variable (e : ι → L) (h : κ → L)

-- The algebra equivalence supplies bijectivity; the two coalgebra laws are checked below.
private noncomputable def kostantFormBaseChangeAlgEquiv
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤) :
    ℚ ⊗[ℤ] (kostantForm e h) ≃ₐ[ℚ] U :=
  Subring.ratBaseChangeEquiv _ (span_kostantForm_eq_top e h hgen)

private theorem kostantFormBaseChangeAlgEquiv_tmul
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤)
    (q : ℚ) (x : kostantForm e h) :
    kostantFormBaseChangeAlgEquiv e h hgen (q ⊗ₜ[ℤ] x) = q • (x : U) :=
  Subring.ratBaseChangeEquiv_tmul _ _ q x

private theorem kostantFormBaseChangeAlgEquiv_counit
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤) :
    (Bialgebra.counitAlgHom ℚ U).comp
        (kostantFormBaseChangeAlgEquiv e h hgen).toAlgHom =
      Bialgebra.counitAlgHom ℚ (ℚ ⊗[ℤ] kostantForm e h) := by
  apply Algebra.TensorProduct.ext'
  intro q x
  simp [kostantFormBaseChangeAlgEquiv_tmul, kostantForm_counit, mul_comm]

-- Distributing scalar extension over the integral tensor square agrees with the existing
-- faithful integral-to-rational tensor comparison. This is specific to the Kostant inclusion.
private theorem kostantFormBaseChangeAlgEquiv_tensor
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤)
    (q : ℚ) (t : kostantForm e h ⊗[ℤ] kostantForm e h) :
    Algebra.TensorProduct.map (kostantFormBaseChangeAlgEquiv e h hgen).toAlgHom
        (kostantFormBaseChangeAlgEquiv e h hgen).toAlgHom
        (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ ℚ
          (kostantForm e h) (kostantForm e h) (q ⊗ₜ[ℤ] t)) =
      q • kostantTensorMap e h t := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
  | tmul x y =>
      simp [kostantFormBaseChangeAlgEquiv_tmul, kostantTensorMap_tmul,
        TensorProduct.smul_tmul']

private theorem kostantFormBaseChangeAlgEquiv_comul
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤) :
    (Algebra.TensorProduct.map (kostantFormBaseChangeAlgEquiv e h hgen).toAlgHom
        (kostantFormBaseChangeAlgEquiv e h hgen).toAlgHom).comp
        (Bialgebra.comulAlgHom ℚ (ℚ ⊗[ℤ] kostantForm e h)) =
      (Bialgebra.comulAlgHom ℚ U).comp
        (kostantFormBaseChangeAlgEquiv e h hgen).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro q x
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, AlgEquiv.coe_toAlgHom,
    Coalgebra.baseChange_comul_tmul, kostantForm_comul, AlgHom.toLinearMap_apply,
    kostantFormBaseChangeAlgEquiv_tensor, kostantTensorMap_kostantFormComul_apply,
    kostantFormBaseChangeAlgEquiv_tmul, map_smul]

/-- **The Kostant form is an integral Hopf form of the enveloping algebra.** Extending its scalars
from `ℤ` to `ℚ` recovers `U(L)`, compatibly with multiplication, comultiplication, counit, and
antipode. No integral PBW basis or freeness assertion is required. -/
noncomputable def kostantFormBaseChange
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤) :
    ℚ ⊗[ℤ] (kostantForm e h) ≃ₐc[ℚ] U :=
  BialgEquiv.ofAlgEquiv (kostantFormBaseChangeAlgEquiv e h hgen)
    (kostantFormBaseChangeAlgEquiv_counit e h hgen)
    (kostantFormBaseChangeAlgEquiv_comul e h hgen)

/-- The rational Hopf comparison sends a pure tensor to the scalar multiple of its underlying
integral element. -/
@[simp]
theorem kostantFormBaseChange_tmul
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤)
    (q : ℚ) (x : kostantForm e h) :
    kostantFormBaseChange e h hgen (q ⊗ₜ[ℤ] x) = q • (x : U) :=
  kostantFormBaseChangeAlgEquiv_tmul e h hgen q x

/-- The Kostant form allows denominators to be cleared: every element of the enveloping algebra is
carried into it by some nonzero natural number. -/
theorem exists_natCast_smul_mem_kostantForm
    (hgen : LieSubalgebra.lieSpan ℚ L (Set.range e ∪ Set.range h) = ⊤) (u : U) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • u ∈ kostantForm e h :=
  Subring.exists_natCast_smul_mem _ (span_kostantForm_eq_top e h hgen) u

end TauCeti.UniversalEnvelopingAlgebra
