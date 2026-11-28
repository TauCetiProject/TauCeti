/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.FrameFor
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.TorsionClass

/-!
# Frames of hermitian spaces with an adelic frame

Let `V = (J, x)` be a hermitian space with an adelic frame over a CM field `E`
(`TauCeti.FramedHermitianSpace`), and `x_f` the finite component of its frame. The finite frame
equation `x_f* J x_f = 1` says that `x_f` is a frame for `J` in the sense of `TauCeti.IsFrameFor`,
with `ε = 1`, and the lattice `Λ_V = {y ∈ Eⁿ : x_f⁻¹ y ∈ Ôⁿ}` of `V` is the module
`Eⁿ ∩ x_f Ôⁿ = Matrix.GeneralLinearGroup.frameLattice x_f`, so it inherits the API of frame
lattices (finite generation, spanning, the torsion-class description).

## Main results

* `TauCeti.FramedHermitianSpace.isFrameFor_gram`: `x_f` is a frame for `J`.
* `TauCeti.FramedHermitianSpace.lattice_eq_frameLattice`: `Λ_V = Eⁿ ∩ x_f Ôⁿ`.
-/

public section

open Matrix NumberField
open scoped NumberField.AdeleRing

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n]
  [DecidableEq n]

namespace FramedHermitianSpace

variable {s : n → ℤˣ} (V : FramedHermitianSpace E s)

/-- The finite component of the frame of a hermitian space with an adelic frame is a frame for
its Gram matrix, with `ε = 1`. -/
theorem isFrameFor_gram : IsFrameFor E V.gram V.frame.2 :=
  isFrameFor_iff.2 ⟨1, by simpa using V.star_mul_gram_mul_snd⟩

/-- The lattice `Λ_V` of a hermitian space with an adelic frame is `Eⁿ ∩ x_f Ôⁿ` for the finite
component `x_f` of its frame. -/
theorem lattice_eq_frameLattice : V.lattice = V.frame.2.frameLattice := by
  ext y
  simp only [mem_lattice_iff, GeneralLinearGroup.mem_frameLattice_iff, Function.comp_def]

end FramedHermitianSpace

end TauCeti
