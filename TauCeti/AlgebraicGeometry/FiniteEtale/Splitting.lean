/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.RingTheory.Etale.Splitting

/-!
# Splitting finite étale schemes over a field

Every finite étale scheme over a field becomes the spectrum of a finite product of `n` copies
of the base field after a finite Galois extension whose degree divides `n!`. The isomorphism
is over the extended base, so it labels all points as rational points, including their scheme
structures.
The empty scheme corresponds to the product indexed by `Fin 0`.

This is the scheme form of `TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct`, transported
through `TauCeti.FiniteEtaleScheme.spec` and Mathlib's affine pullback comparison.

## References

* The Stacks Project, Tag 03QR (schemes étale over a point).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite étale scheme becomes a disjoint union of `n` rational points after a finite
Galois field extension of degree dividing `n!`. The splitting is an isomorphism over the
extended base. -/
theorem exists_split_of_isFinite_of_etale {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L) (n : ℕ),
      Module.finrank K L ∣ n.factorial ∧
        Nonempty (Over.mk (pullback.snd f (Spec.algebraMap K L)) ≅
          Over.mk (Spec.algebraMap L (Fin n → L))) := by
  obtain ⟨A, ⟨e₀⟩⟩ := f.exists_finiteEtale_algebra
  obtain ⟨L, _, _, _, _, hdeg, hL⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K A.obj
  obtain ⟨n, ⟨a⟩⟩ := hL.nonempty_algEquiv_fun
  have hn : Module.finrank K A.obj = n := by
    rw [← Module.finrank_baseChange (R := L), a.toLinearEquiv.finrank_eq]
    simp
  let e₁ :=
    TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv K A.obj L (Fin n → L) a
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, hn ▸ hdeg,
    ⟨((Over.pullback (Spec.algebraMap K L)).mapIso e₀).symm ≪≫ e₁⟩⟩

end AlgebraicGeometry.Scheme.Hom
