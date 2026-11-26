/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import TauCeti.AlgebraicGeometry.Compactification.Basic
import TauCeti.AlgebraicGeometry.AffineSpace.Immersion
import TauCeti.AlgebraicGeometry.Compactification.Immersion
import TauCeti.AlgebraicGeometry.Compactification.ProjectiveClosure

/-!
# Compactifying quasi-affine schemes

Finite-dimensional affine space over any scheme is compactifiable by base change of the
projective closure over the integers. A quasi-compact morphism locally of finite type
from a quasi-affine scheme then has a dense compactification. Take the schematic closure
of its immersion into relative affine space in this compactification.

This gives the compactifications of the individual affine charts used in the proof of
Nagata's theorem (Stacks Project, Theorem 38.33.8, Tag 0F41).
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace AffineSpace

/-- The projection from finite-dimensional affine space over any scheme is compactifiable. -/
theorem nonempty_compactification_over (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    Nonempty (TauCeti.Compactification (𝔸(ι; S) ↘ S)) := by
  let S₀ := Spec (.of (ULift.{u} ℤ))
  let g : S ⟶ S₀ := specULiftZIsTerminal.from S
  let p : 𝔸(ι; S₀) ⟶ S₀ := 𝔸(ι; S₀) ↘ S₀
  have : Smooth p := (smoothOfRelativeDimension ι S₀).smooth
  have : LocallyOfFiniteType p :=
    ⟨fun {_} hU {_} hV e ↦
      RingHom.FiniteType.of_finitePresentation (p.smooth_appLE hU hV e).finitePresentation⟩
  obtain ⟨C⟩ := TauCeti.nonempty_denseCompactification_of_isAffine p
  let h := isPullback_map (n := ι) g
  exact ⟨(C.obj.baseChange g).precomp h.isoPullback.hom h.isoPullback_hom_snd⟩

end AffineSpace

/-- A quasi-compact morphism locally of finite type from a quasi-affine scheme has a
schematically dense compactification over its target. -/
theorem Scheme.Hom.nonempty_denseCompactification_of_isQuasiAffine
    {X S : Scheme.{u}} [X.IsQuasiAffine] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (TauCeti.DenseCompactification f) := by
  obtain ⟨ι, hι, i, hi, fac⟩ := f.exists_isImmersion_affineSpace
  have : QuasiCompact (i ≫ 𝔸(ι; S) ↘ S) := fac ▸ ‹QuasiCompact f›
  have : QuasiCompact i := QuasiCompact.of_comp i (𝔸(ι; S) ↘ S)
  exact TauCeti.nonempty_denseCompactification_of_isImmersion i fac
    (AffineSpace.nonempty_compactification_over ι S)

end AlgebraicGeometry
