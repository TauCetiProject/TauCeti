/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.FixedSubalgebra.Basic
public import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism

/-!
# Fixed subalgebras of the native Serre diagram action

A Serre realization intertwines the native diagram automorphism with any endomorphism
that performs the same reindexing on its three generator families. It therefore
restricts to their fixed Lie subalgebras. If this particular realization is an
equivalence, its restriction is an equivalence as well.

-/

public section

namespace TauCeti

variable {B R L : Type*} [DecidableEq B] [CommRing R]
  [LieRing L] [LieAlgebra R L] {CM : Matrix B B ℤ} {σ : Equiv.Perm B}
  {H E F : B → L} (h : IsSerreSystem R CM H E F)
  (hσ : CM.submatrix σ σ = CM) (ψ : L →ₗ⁅R⁆ L)
  (hH : ∀ i, ψ (H i) = H (σ i))
  (hE : ∀ i, ψ (E i) = E (σ i))
  (hF : ∀ i, ψ (F i) = F (σ i))

include hH hE hF in
/-- The generator equations imply equivariance of the actual Serre realization. -/
theorem serreLift_intertwines_diagramAut :
    ψ.comp (serreLift h) = (serreLift h).comp (serreDiagramAut R CM hσ).toLieHom :=
  serre_hom_ext (fun i => by simp [hH]) (fun i => by simp [hE])
    (fun i => by simp [hF])

/-- A Serre realization restricts to the fixed subalgebra of its native diagram action. -/
noncomputable def serreLiftFixed :
    (serreDiagramAut R CM hσ).toLieHom.fixedSubalgebra →ₗ⁅R⁆ ψ.fixedSubalgebra :=
  LieHom.restrictFixed (serreLift h) (serreLift_intertwines_diagramAut h hσ ψ hH hE hF)

@[simp]
theorem coe_serreLiftFixed
    (x : (serreDiagramAut R CM hσ).toLieHom.fixedSubalgebra) :
    (serreLiftFixed h hσ ψ hH hE hF x : L) = serreLift h x :=
  LieHom.coe_restrictFixed _ _ _

/-- A Serre realization that is an equivalence identifies the two fixed Lie subalgebras. -/
noncomputable def serreEquivFixed (e : Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ L)
    (he : e.toLieHom = serreLift h) :
    (serreDiagramAut R CM hσ).toLieHom.fixedSubalgebra ≃ₗ⁅R⁆ ψ.fixedSubalgebra :=
  e.restrictFixed (by rw [he]; exact serreLift_intertwines_diagramAut h hσ ψ hH hE hF)

@[simp]
theorem serreEquivFixed_apply (e : Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ L)
    (he : e.toLieHom = serreLift h)
    (x : (serreDiagramAut R CM hσ).toLieHom.fixedSubalgebra) :
    serreEquivFixed h hσ ψ hH hE hF e he x = serreLiftFixed h hσ ψ hH hE hF x := by
  apply Subtype.ext
  simpa [serreEquivFixed] using DFunLike.congr_fun he (x : Matrix.ToLieAlgebra R CM)

@[simp]
theorem coe_serreEquivFixed_symm (e : Matrix.ToLieAlgebra R CM ≃ₗ⁅R⁆ L)
    (he : e.toLieHom = serreLift h) (y : ψ.fixedSubalgebra) :
    ((serreEquivFixed h hσ ψ hH hE hF e he).symm y : Matrix.ToLieAlgebra R CM) =
      e.symm y :=
  LieEquiv.coe_restrictFixed_symm _ _ _

end TauCeti
