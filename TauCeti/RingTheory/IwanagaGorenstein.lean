/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.Module.Injective.DivisionRing
public import TauCeti.RingTheory.GlobalDimension
public import TauCeti.RingTheory.Noetherian.MulOpposite
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.Algebra.Homology.Ext.Equivalence
import TauCeti.RingTheory.GlobalDimension.MulOpposite
import TauCeti.RingTheory.Regular.InjectiveDimension

/-!
# Iwanaga–Gorenstein rings

A ring `A` is **Iwanaga–Gorenstein** when it is left and right noetherian and the regular module
has finite injective dimension on both sides. Right modules are left `Aᵐᵒᵖ`-modules, so the
right-hand conditions are stated for `Aᵐᵒᵖ`. These are the rings of Buchweitz's comparison between
Gorenstein-projective modules and the singularity category.

A left and right noetherian ring that is self-injective on both sides, a quasi-Frobenius ring, is
Iwanaga–Gorenstein with both injective dimensions zero
(`TauCeti.IsIwanagaGorenstein.of_injective`). In particular division rings are
Iwanaga–Gorenstein. More generally, any left and right noetherian ring of finite global dimension
is Iwanaga–Gorenstein (`TauCeti.IsIwanagaGorenstein.of_globalDimension_lt_top`), since its left
and right global dimensions coincide by Auslander's theorem; this covers noetherian regular
commutative rings of finite Krull dimension and, in particular, regular local rings. Finally, if
`R` is an Iwanaga–Gorenstein commutative ring and `x` is a nonzerodivisor of `R`, then the
hypersurface quotient `R ⧸ (x)` is again Iwanaga–Gorenstein
(`TauCeti.IsIwanagaGorenstein.quotient_span_singleton`).

## Main definitions and results

* `TauCeti.IsIwanagaGorenstein`: left and right noetherian with both self-injective dimensions
  finite.
* `TauCeti.IsIwanagaGorenstein.of_commRing`: for a commutative noetherian ring, finite left
  self-injective dimension suffices.
* `TauCeti.IsIwanagaGorenstein.of_globalDimension_lt_top` and
  `TauCeti.IsIwanagaGorenstein.of_hasProjectiveDimensionLE`: left and right noetherian rings of
  finite global dimension are Iwanaga–Gorenstein.
* `TauCeti.IsIwanagaGorenstein.of_isRegularRing`: noetherian regular commutative rings of finite
  Krull dimension (in particular regular local rings) are Iwanaga–Gorenstein.
* `TauCeti.IsIwanagaGorenstein.quotient_span_singleton`: the quotient of a commutative
  Iwanaga–Gorenstein ring by a nonzerodivisor is Iwanaga–Gorenstein.

## References

* Yasuo Iwanaga, *On rings with finite self-injective dimension*, Comm. Algebra **7** (1979).
* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 9.1.
* D. Rees, *A theorem of homological algebra*, Proc. Cambridge Philos. Soc. **52** (1956), 605–610.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

/-- A ring is **Iwanaga–Gorenstein** if it is left and right noetherian and the regular module has
finite injective dimension both as a left and as a right module. -/
class IsIwanagaGorenstein (A : Type u) [Ring A] : Prop where
  isNoetherianRing : IsNoetherianRing A
  isNoetherianRing_op : IsNoetherianRing Aᵐᵒᵖ
  exists_hasInjectiveDimensionLE : ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of A A) n
  exists_hasInjectiveDimensionLE_op : ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of Aᵐᵒᵖ A) n

namespace IsIwanagaGorenstein

attribute [instance] isNoetherianRing isNoetherianRing_op

/-- **Quasi-Frobenius rings are Iwanaga–Gorenstein**: a left and right noetherian ring that is
self-injective on both sides has both self-injective dimensions zero. -/
theorem of_injective (A : Type u) [Ring A] [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    [Module.Injective A A] [Module.Injective Aᵐᵒᵖ A] : IsIwanagaGorenstein A where
  isNoetherianRing := inferInstance
  isNoetherianRing_op := inferInstance
  exists_hasInjectiveDimensionLE := by
    have := Module.injective_object_of_injective_module A A
    exact ⟨0, inferInstance⟩
  exists_hasInjectiveDimensionLE_op := by
    have := Module.injective_object_of_injective_module Aᵐᵒᵖ A
    exact ⟨0, inferInstance⟩

/-- Division rings are Iwanaga–Gorenstein. -/
instance (D : Type u) [DivisionRing D] : IsIwanagaGorenstein D :=
  of_injective D

/-- For a commutative noetherian ring, finite injective dimension of the regular module on one
side implies `IsIwanagaGorenstein`: `RingEquiv.toOpposite` identifies left and right modules. -/
theorem of_commRing (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of R R) n) : IsIwanagaGorenstein R where
  isNoetherianRing := inferInstance
  isNoetherianRing_op := inferInstance
  exists_hasInjectiveDimensionLE := h
  exists_hasInjectiveDimensionLE_op := by
    obtain ⟨n, hn⟩ := h
    let e : Rᵐᵒᵖ ≃+* R := (RingEquiv.toOpposite R).symm
    have : HasInjectiveDimensionLE
        ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of R R)) n :=
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).hasInjectiveDimensionLT_functor_obj_iff
        (ModuleCat.of R R) (n + 1)).mpr hn
    let opIso : ModuleCat.of Rᵐᵒᵖ Rᵐᵒᵖ ≅ ModuleCat.of Rᵐᵒᵖ R :=
      LinearEquiv.toModuleIso
        { toFun := MulOpposite.unop
          invFun := MulOpposite.op
          left_inv := MulOpposite.op_unop
          right_inv := MulOpposite.unop_op
          map_add' := MulOpposite.unop_add
          map_smul' := fun _ _ ↦ rfl }
    exact ⟨n, hasInjectiveDimensionLT_of_iso
      (ModuleCat.restrictScalarsIsoOfEquiv e ≪≫ opIso) (n + 1)⟩

/-- **Noetherian rings of finite global dimension are Iwanaga–Gorenstein.** By Auslander's theorem
(`TauCeti.globalDimension_mulOpposite`), left and right global dimensions agree, bounding both
self-injective dimensions. -/
theorem of_globalDimension_lt_top (A : Type u) [Ring A] [IsNoetherianRing A]
    [IsNoetherianRing Aᵐᵒᵖ] (h : globalDimension.{u} A < ⊤) : IsIwanagaGorenstein A := by
  have ⟨n, hn⟩ : ∃ n : ℕ, globalDimension.{u} A ≤ n := by
    induction hd : globalDimension.{u} A using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe d =>
      induction d with
      | top => exact absurd hd h.ne
      | coe n => exact ⟨n, le_rfl⟩
  exact
    { isNoetherianRing := inferInstance
      isNoetherianRing_op := inferInstance
      exists_hasInjectiveDimensionLE :=
        ⟨n, (globalDimension_le_iff_hasInjectiveDimensionLE A n).mp hn _⟩
      exists_hasInjectiveDimensionLE_op :=
        ⟨n, (globalDimension_le_iff_hasInjectiveDimensionLE Aᵐᵒᵖ n).mp
          ((globalDimension_mulOpposite A).trans_le hn) _⟩ }

/-- A left and right noetherian ring over which every left module in the ring's universe has
projective dimension at most `d` is Iwanaga–Gorenstein. -/
theorem of_hasProjectiveDimensionLE (A : Type u) [Ring A] [IsNoetherianRing A]
    [IsNoetherianRing Aᵐᵒᵖ] (d : ℕ)
    (hd : ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M d) : IsIwanagaGorenstein A :=
  of_globalDimension_lt_top A <|
    ((globalDimension_le_iff_hasProjectiveDimensionLE A d).mpr hd).trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))

/-- **Regular rings of finite Krull dimension are Iwanaga–Gorenstein**: their global dimension is
at most their Krull dimension (`ModuleCat.projectiveDimension_le_ringKrullDim`). -/
theorem of_isRegularRing (R : Type u) [CommRing R] [IsRegularRing R]
    (h : ringKrullDim R < ⊤) : IsIwanagaGorenstein R :=
  of_globalDimension_lt_top R <|
    ((globalDimension_le_iff R _).mpr ModuleCat.projectiveDimension_le_ringKrullDim).trans_lt h

/-- A regular commutative ring with `[FiniteRingKrullDim R]` is Iwanaga–Gorenstein. -/
theorem of_isRegularRing_of_finiteRingKrullDim (R : Type u) [CommRing R] [IsRegularRing R]
    [FiniteRingKrullDim R] : IsIwanagaGorenstein R :=
  of_isRegularRing R ringKrullDim_lt_top

/-- Regular local rings are Iwanaga–Gorenstein. -/
instance (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsIwanagaGorenstein R :=
  of_globalDimension_lt_top R IsRegularLocalRing.globalDimension_lt_top

/-- **Hypersurface quotients of Iwanaga–Gorenstein commutative rings.** If `R` is a commutative
Iwanaga–Gorenstein ring and `x` is a nonzerodivisor of `R`, then `R ⧸ (x)` is Iwanaga–Gorenstein.
-/
theorem quotient_span_singleton {R : Type u} [CommRing R] [IsIwanagaGorenstein R] {x : R}
    (hx : x ∈ nonZeroDivisors R) : IsIwanagaGorenstein (R ⧸ Ideal.span {x}) := by
  obtain ⟨n, _⟩ := exists_hasInjectiveDimensionLE (A := R)
  exact of_commRing _ ⟨n, ModuleCat.hasInjectiveDimensionLE_quotient_span_singleton hx n⟩

end IsIwanagaGorenstein

end TauCeti
