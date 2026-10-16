/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.MulAut
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Automorphism

/-!
# Continuous automorphisms of a free pro-`p` group and `GL_n(𝔽_p)`

Let `F = freeProP p X` be the free pro-`p` group on a finite type `X`, and `Φ(F)` its Frattini
subgroup. The Frattini quotient `F ⧸ Φ(F)` is an `𝔽_p`-vector space with basis the classes of the
generators (`TauCeti.freeProP.frattiniQuotientBasis`), and a continuous automorphism `φ` of `F`
induces an automorphism of it (`TauCeti.ContinuousAut.mapQuotient`), which is `𝔽_p`-linear
(`TauCeti.mulAutEquivZModLinearEquiv`). Its matrix in the basis of generator classes
(`Module.Basis.toGL`) defines a group homomorphism

  `ContinuousAut F →* GL X 𝔽_p`,

whose `j`-th column holds the coordinates of the class of `φ (of j)`.

This homomorphism is surjective: every automorphism of the Frattini quotient lifts to a continuous
automorphism of `F` (`TauCeti.freeProP.mapQuotient_proPFrattini_surjective`, by Burnside's basis
theorem and the Hopf property). For `X = Fin 2` this is the surjection
`ContinuousAut F →* GL_2(𝔽_p)`. Its kernel is the group of continuous automorphisms acting
trivially on the Frattini quotient, which is open and pro-`p` in the congruence topology
(`TauCeti.ContinuousAut.isOpen_ker_mapQuotient_proPFrattini`,
`TauCeti.IsProP.isProP_ker_mapQuotient_proPFrattini`).

## Main definitions

* `TauCeti.freeProP.continuousAutToGL`: the matrix of the action of a continuous automorphism of
  `freeProP p X` on its Frattini quotient, as a homomorphism to `GL X (ZMod p)`.

## Main results

* `TauCeti.freeProP.continuousAutToGL_apply`: the `(i, j)` entry of the matrix of `φ` is the
  `i`-th coordinate of the class of `φ (of j)`.
* `TauCeti.freeProP.continuousAutToGL_surjective`: every matrix in `GL X (ZMod p)` is the matrix
  of a continuous automorphism.
* `TauCeti.freeProP.ker_continuousAutToGL`: the kernel consists of the automorphisms acting
  trivially on the Frattini quotient.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 4.5.
-/

public section

namespace TauCeti

universe u

namespace freeProP

variable (p : ℕ) [Fact p.Prime] (X : Type u) [Fintype X] [DecidableEq X]

/-- The action of a continuous automorphism of the free pro-`p` group on `X` on its Frattini
quotient, as an invertible matrix over `𝔽_p` in the basis of the classes of the generators. -/
noncomputable def continuousAutToGL : ContinuousAut (freeProP p X) →* GL X (ZMod p) :=
  (frattiniQuotientBasis p X).toGL.toMonoidHom.comp
    ((mulAutEquivZModLinearEquiv p _).toMonoidHom.comp
      (ContinuousAut.mapQuotient (isTopCharacteristic_proPFrattini (G := freeProP p X) p)))

variable {p X}

/-- The `(i, j)` entry of the matrix of `φ` is the `i`-th coordinate of the class of `φ (of j)`
in the basis of the classes of the generators. -/
@[simp]
theorem continuousAutToGL_apply (φ : ContinuousAut (freeProP p X)) (i j : X) :
    (continuousAutToGL p X φ : Matrix X X (ZMod p)) i j =
      (frattiniQuotientBasis p X).repr
        (Additive.ofMul (φ (of j) : freeProP p X ⧸ proPFrattini p (freeProP p X))) i := by
  simp [continuousAutToGL, LinearMap.toMatrix_apply]

/-- **Every invertible matrix over `𝔽_p` comes from a continuous automorphism** of the free
pro-`p` group of finite rank: the automorphism of the Frattini quotient it defines lifts. -/
theorem continuousAutToGL_surjective : Function.Surjective (continuousAutToGL p X) :=
  (frattiniQuotientBasis p X).toGL.surjective.comp
    ((mulAutEquivZModLinearEquiv p _).surjective.comp mapQuotient_proPFrattini_surjective)

/-- The kernel of `continuousAutToGL` is the group of continuous automorphisms acting trivially
on the Frattini quotient. -/
@[simp]
theorem ker_continuousAutToGL :
    (continuousAutToGL p X).ker =
      (ContinuousAut.mapQuotient (isTopCharacteristic_proPFrattini (G := freeProP p X) p)).ker := by
  ext φ
  simp [continuousAutToGL]

end freeProP

end TauCeti
