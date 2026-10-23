/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.AffinePushforward
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra

/-!
# Coherent cohomology of finite covers of the projective line

Let `X` be finite over `ℙ¹_R`, where `R` is Noetherian. Every quasicoherent sheaf of finite
type on `X` has finitely generated cohomology over `R` in every degree, and its cohomology
vanishes above degree one. No flatness or reducedness assumption is imposed on `X` or the
coefficient sheaf. In particular this applies to the finite normalization maps from regular
curve models to `ℙ¹`.

Finite pushforward preserves coherent sheaves. The zeroth and first cohomology calculations
transfer along the two standard affine charts, while the same cover and its affine overlap
kill higher cohomology.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 8.1 and Theorem 5.2.
* The Stacks Project, Tag 02O6, finiteness of cohomology of coherent sheaves on proper schemes.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

private lemma exists_two_affine_opens_projectiveLine (R : Type u) [CommRing R] :
    ∃ U V : (projectiveLine R).Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ :=
  ⟨_, _, Proj.isAffineOpen_basicOpen _ _ (projectiveLine.coord_mem R 0) one_pos,
    Proj.isAffineOpen_basicOpen _ _ (projectiveLine.coord_mem R 1) one_pos,
    projectiveLine.basicOpen_coord_sup_eq_top R⟩

/-- A quasicoherent sheaf on a locally Noetherian scheme affine over the projective line
has no cohomology in degrees at least two. -/
theorem subsingleton_cohomology_of_two_le_of_isAffineHom_to_projectiveLine
    (R : Type u) [CommRing R] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ projectiveLine R) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Cohomology M n) := by
  obtain ⟨U, V, hU, hV, hUV⟩ := exists_two_affine_opens_projectiveLine R
  exact subsingleton_cohomology_of_two_le_of_isAffineOpen M (hU.preimage f) (hV.preimage f)
    (by rw [← f.preimage_inf]; exact (hU.inf hV).preimage f)
    (f.preimage_sup_eq_top hUV) n hn

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} [X.Over (Spec (.of R))]
  (f : X ⟶ projectiveLine R) [IsFinite f] [f.IsOver (Spec (.of R))]

include f

/-- Every cohomology group of a quasicoherent sheaf of finite type on a scheme finite over
`ℙ¹_R` is finite over the Noetherian ring `R`. Neither the morphism nor the coefficient
sheaf needs to be flat over `R`. -/
theorem finite_cohomology_of_isFinite_to_projectiveLine (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) : Module.Finite R (Cohomology M n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let N : SheafOfModules (projectiveLine R).ringCatSheaf := (pushforward f).obj M
  have : N.IsFinitePresentation := isFinitePresentation_pushforward_of_isFinite f M
  have : N.IsFiniteType := inferInstance
  have := projectiveLine.finite_cohomology R N
  cases n with
  | zero => exact (f.moduleFinite_cohomology_zero_pushforward_iff (R := R) M).mp inferInstance
  | succ n =>
    cases n with
    | zero =>
      obtain ⟨U, V, hU, hV, hUV⟩ := exists_two_affine_opens_projectiveLine R
      exact (f.moduleFinite_cohomology_one_pushforward_iff_of_two_affine_opens (R := R)
        M U V hU hV hUV).mp inferInstance
    | succ n =>
      have := subsingleton_cohomology_of_two_le_of_isAffineHom_to_projectiveLine R f M (n + 2)
        (by omega)
      infer_instance

end AlgebraicGeometry.Scheme.Modules
