/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf

/-!
# Example: the zero module gives the zero big module

For a quasi-coherent `𝒪_S`-module `F`, the big-site module `F^a : (T, h) ↦ Γ(T, h^* F)` is
`AlgebraicGeometry.Scheme.Modules.bigSheaf F`. If `F` is zero then so is every pullback `h^* F`,
as pullback is a left adjoint, so every `Γ(T, h^* F)` is zero and `0^a = 0`.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace TauCeti.AlgebraicGeometry.BigSheafZeroExample

variable {S : Scheme.{u}} {F : S.Modules} [F.IsQuasicoherent]

omit [F.IsQuasicoherent] in
/-- The sections `Γ(T, h^* F)` of the big presheaf of a zero module vanish. -/
theorem eq_zero_of_isZero (hF : IsZero F) (T : Over S) (x : F.bigPresheaf.obj (op T)) :
    x = 0 := by
  have hz := Functor.map_isZero (Modules.pullback T.hom) hF
  exact congr($(hz.eq_of_src (𝟙 _) 0).val.app (op ⊤) x)

/-- **`0^a = 0`.** The big-site module of a zero quasi-coherent module is zero. -/
theorem isZero_bigSheaf (hF : IsZero F) : IsZero (Modules.bigSheaf F) := by
  rw [IsZero.iff_id_eq_zero]
  ext T x
  exact (eq_zero_of_isZero hF T.unop x).trans (eq_zero_of_isZero hF T.unop _).symm

end TauCeti.AlgebraicGeometry.BigSheafZeroExample
