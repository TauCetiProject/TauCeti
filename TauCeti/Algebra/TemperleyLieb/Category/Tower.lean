/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Category.Algebra
public import TauCeti.Algebra.TemperleyLieb.Category.Monoidal
import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# The tower of Temperley–Lieb diagram algebras

The inclusion `TauCeti.TLAlg.incl R δ n` adds one straight strand on the right of a diagram
on `n` strands. It is an algebra homomorphism because right tensoring is an additive linear
functor. On the diagram basis it inserts the matching of a single straight strand between the
bottom and top boundaries, without creating a circle or changing a coefficient.

`TauCeti.TLAlg.incl_injective` proves injectivity over every commutative ring, at every loop
value, including zero: right tensoring in the linear diagram category is faithful. These
inclusions are the tower maps used to formulate the Markov property of a diagrammatic trace.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.TLAlg

universe u

variable (R : Type u) [CommRing R] (δ : R) (n : ℕ)

/-- The tower inclusion of diagram algebras, adding a straight strand on the right. -/
noncomputable def incl : TLAlg R δ n →ₐ[R] TLAlg R δ (n + 1) :=
  (tensorRight (TLCat.of 1 : TLCat R δ)).mapEndAlgHom R (TLCat.of n)

/-- The tower inclusion acts on underlying morphisms by right whiskering with one strand. -/
@[simp]
theorem asHom_incl (x : TLAlg R δ n) :
    (incl R δ n x).asHom = x.asHom ▷ (TLCat.of 1 : TLCat R δ) := by
  simpa only [incl, Functor.flip_obj_map, curriedTensor_map_app] using
    (tensorRight (TLCat.of 1 : TLCat R δ)).mapEndAlgHom_asHom R (TLCat.of n) x

/-- A basis diagram is sent to the basis diagram obtained by adding a rightmost straight
strand. In particular no power of the loop parameter is introduced. -/
@[simp]
theorem incl_diagBasis (x : PlanarMatching (n + n)) :
    incl R δ n (End.of (TLCat.diagBasis (TLCat.of n) (TLCat.of n) x)) =
      End.of (TLCat.diagBasis (TLCat.of (n + 1)) (TLCat.of (n + 1))
        (TLDiagram.tensor ⟨x, 0⟩ (TLDiagram.id 1)).matching) := by
  apply End.ext
  rw [asHom_incl]
  -- Reduce the asHom projections of the two End.of constructors.
  dsimp only
  -- Tensoring objects adds their strand counts: of n ⊗ of 1 is of (n + 1).
  exact TLCat.diagBasis_whiskerRight x (TLCat.of 1 : TLCat R δ)

/-- Adding a straight strand on the right preserves each existing generator. -/
@[simp]
theorem incl_e (i : Fin (n - 1)) :
    incl R δ n (e R δ i) = e R δ (Fin.castLE (by omega) i) := by
  apply End.ext
  rw [asHom_incl, asHom_e_eq_diagBasis, asHom_e_eq_diagBasis,
    TLCat.diagBasis_whiskerRight]
  -- Tensoring objects adds their strand counts, so both basis vectors have the same endpoints.
  congr 1
  have he : (⟨(TLDiagCat.e n i).diagram.matching, 0⟩ : TLDiagram n n) =
      (TLDiagCat.e n i).diagram :=
    TLDiagram.ext rfl (TLDiagCat.circles_e n i).symm
  rw [he]
  exact congrArg TLDiagram.matching (TLDiagCat.diagram_e_tensor_id n i)

/-- Adding a strand preserves all coefficients, pushing them forward along the injection
of planar matchings. -/
theorem coeff_incl (x : TLAlg R δ n) :
    (incl R δ n x).asHom.coeff = Finsupp.mapDomain
      (fun y => (TLDiagram.tensor ⟨y, 0⟩ (TLDiagram.id 1)).matching) x.asHom.coeff := by
  rw [asHom_incl, TLCat.coeff_whiskerRight]

/-- The diagram-algebra tower inclusions are injective at every loop value over every
commutative ring, with no nontriviality or invertibility assumption. -/
theorem incl_injective : Function.Injective (incl R δ n) :=
  (tensorRight (TLCat.of 1 : TLCat R δ)).mapEndAlgHom_injective R (TLCat.of n)

end TauCeti.TLAlg
