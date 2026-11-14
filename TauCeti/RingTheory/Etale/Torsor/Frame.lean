/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
public import TauCeti.RingTheory.Etale.Torsor.Descent
public import TauCeti.RingTheory.Unramified.Frame.Universal

/-!
# The frame algebra of a finite étale algebra is a splitting torsor

Let `S` be an `R`-algebra which becomes split of rank `|ι|` after a faithfully flat extension
`R → T`, that is `T ⊗[R] S ≃ₐ[T] (ι → T)`. Then the frame algebra
`TauCeti.Algebra.FrameAlgebra R S ι` of `ι`-tuples of pairwise distinct points of `Spec S` is a
finite étale `Equiv.Perm ι`-torsor over `R`
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`).

Indeed, forming frame algebras commutes with base change
(`TauCeti.Algebra.FrameAlgebra.baseChangeEquiv`), so `T ⊗[R] FrameAlgebra R S ι` is the frame
algebra of the split algebra `ι → T`, which is the trivial torsor `Equiv.Perm ι → T`
(`TauCeti.Algebra.FrameAlgebra.permEquiv`); being a torsor descends along faithfully flat
extensions (`TauCeti.Algebra.IsFiniteEtaleTorsor.of_baseChange_algEquiv_pi`).

Every finite étale algebra `S` of constant rank `Fintype.card ι` is split by a faithfully flat
finite étale extension (Mathlib's `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`), so its
frame algebra is a finite étale `Perm ι`-torsor
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`). Moreover, the universal frame
`FrameAlgebra R S ι ⊗[R] S → (ι → FrameAlgebra R S ι)` is an isomorphism of
`FrameAlgebra R S ι`-algebras (`TauCeti.Algebra.FrameAlgebra.universalFrameEquiv`), so `S` becomes
split of constant rank over its frame algebra
(`TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct`,
`TauCeti.Algebra.FrameAlgebra.isTotallySplit_tensorProduct`). This makes the frame algebra the
ring-theoretic Galois closure of `S`: for a finite separable field extension `L / K` of degree `n`
with Galois closure `M`, it is a product of copies of `M`.

The splitting cover in Mathlib is stated for `S` in the universe of `R`. A finite algebra is
isomorphic to one in that universe (`Shrink`), and the frame algebra and universal frame are
invariant under isomorphisms (`TauCeti.Algebra.FrameAlgebra.congr`), so all results hold for `S`
and `ι` in arbitrary universes.

## Main definitions

* `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv`: the universal frame as an isomorphism
  `FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` for `S` finite étale
  of constant rank `Fintype.card ι`.

## Main results

* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`: the frame algebra of an
  algebra split by a faithfully flat extension is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`: the frame algebra of a finite étale algebra
  of constant rank `Fintype.card ι` is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame`: the universal frame of a finite étale
  algebra of constant rank `Fintype.card ι` is bijective.
* `TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct`,
  `TauCeti.Algebra.FrameAlgebra.isTotallySplit_tensorProduct`: a finite étale algebra of constant
  rank `Fintype.card ι` becomes split after base change to `FrameAlgebra R S ι`.
* `TauCeti.Algebra.FrameAlgebra.slotAlgHom_injective_of_etale`: over a nonzero ring, the `|ι|`
  canonical slot maps `S →ₐ[R] FrameAlgebra R S ι` are pairwise distinct.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2), for the Galois closure
  of a connected object of a Galois category.
* H. W. Lenstra, *Galois theory for schemes*, Proposition 5.10, for the splitting cover.
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 15.3.
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti.Algebra

namespace FrameAlgebra

section LocallySplit

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  [Algebra.FormallyUnramified R S] {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Algebra.TensorProduct.rightMulSemiringAction in
/-- **The frame algebra of a locally split algebra is a torsor.** If `S` becomes isomorphic to the
split algebra `ι → T` after a faithfully flat extension `R → T`, then the frame algebra of
`ι`-tuples of pairwise distinct points of `Spec S` is a finite étale `Equiv.Perm ι`-torsor
over `R`. -/
theorem isFiniteEtaleTorsor_of_algEquiv_pi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) :=
  IsFiniteEtaleTorsor.of_baseChange_algEquiv_pi T
    (((baseChangeEquiv R S T ι).trans (congr ι e)).trans (permEquiv T ι)) fun σ x τ ↦ by
      have hσ : MulSemiringAction.toAlgHom R (FrameAlgebra R S ι) σ =
          (permAlgEquiv R S ι σ).toAlgHom :=
        AlgHom.ext (smul_def σ)
      simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.rightMulSemiringAction_smul_def, hσ,
        baseChangeEquiv_map_permAlgEquiv, congr_smul, permEquiv_smul]

end LocallySplit

section Etale

variable {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι]

/-- Over a nontrivial base ring `R : Type u`, every finite étale `R`-algebra `S` (in any universe)
of constant rank `Fintype.card ι` becomes `T`-isomorphic to `ι → T` after a faithfully flat
extension `T : Type u`. -/
private theorem exists_faithfullyFlat_algEquiv_pi [Nontrivial R]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Module.FaithfullyFlat R T),
      Nonempty (T ⊗[R] S ≃ₐ[T] (ι → T)) := by
  have : Small.{u} S := Module.Finite.small R S
  let eS : Shrink.{u} S ≃ₐ[R] S := Shrink.algEquiv R S
  have : Algebra.Etale R (Shrink.{u} S) := .of_equiv eS.symm
  have : Module.Finite R (Shrink.{u} S) := .equiv eS.symm.toLinearEquiv
  have hS' : Module.rankAtStalk (R := R) (Shrink.{u} S) = Fintype.card ι :=
    (Module.rankAtStalk_eq_of_equiv eS.toLinearEquiv).trans h
  obtain ⟨T, _, _, _, _, _, _⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hS'
  obtain ⟨m, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T (T ⊗[R] Shrink.{u} S)
  have : Nontrivial T := (FaithfulSMul.algebraMap_injective R T).nontrivial
  obtain rfl : m = Fintype.card ι := by
    simpa using f.toLinearEquiv.finrank_eq.symm.trans
      (TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq hS')
  exact ⟨T, _, _, inferInstance,
    ⟨((Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) eS.symm).trans f).trans
      (AlgEquiv.piCongrLeft' T (fun _ ↦ T) (Fintype.equivFin ι).symm)⟩⟩

variable [DecidableEq ι]

/-- **The frame algebra is a torsor.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, the frame algebra of `ι`-tuples of pairwise distinct points of `S` is a finite
étale `Perm ι`-torsor over `R`. -/
theorem isFiniteEtaleTorsor (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) := by
  cases subsingleton_or_nontrivial R
  · infer_instance
  obtain ⟨T, _, _, _, ⟨e⟩⟩ := exists_faithfullyFlat_algEquiv_pi h
  exact isFiniteEtaleTorsor_of_algEquiv_pi T e

/-- **The universal frame of a constant-rank finite étale algebra is bijective.** If `S` is finite
étale over `R` of constant rank `Fintype.card ι`, then
`universalFrame R S ι : FrameAlgebra R S ι ⊗[R] S → (ι → FrameAlgebra R S ι)` is bijective. -/
theorem bijective_universalFrame (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Function.Bijective (universalFrame R S ι) := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton (FrameAlgebra R S ι ⊗[R] S) := Module.subsingleton R _
    have : Subsingleton (ι → FrameAlgebra R S ι) := Module.subsingleton R _
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨T, _, _, _, ⟨e⟩⟩ := exists_faithfullyFlat_algEquiv_pi h
  exact bijective_universalFrame_of_algEquiv_pi T e

/-- **The universal frame isomorphism.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, base-changing `S` to `FrameAlgebra R S ι` splits `S` canonically into `ι` copies
of `FrameAlgebra R S ι` along the `ι` slot projections. -/
noncomputable def universalFrameEquiv (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  AlgEquiv.ofBijective (universalFrame R S ι) (bijective_universalFrame h)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv` has underlying map `universalFrame`. -/
@[simp]
theorem coe_universalFrameEquiv (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    ⇑(universalFrameEquiv h) = universalFrame R S ι :=
  (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv` sends `p ⊗ s` at `i` to
`p * slotAlgHom R S i s`. -/
theorem universalFrameEquiv_tmul (h : Module.rankAtStalk (R := R) S = Fintype.card ι)
    (p : FrameAlgebra R S ι) (s : S) (i : ι) :
    universalFrameEquiv h (p ⊗ₜ s) i = p * slotAlgHom R S i s :=
  universalFrame_tmul p s i

/-- A finite étale `R`-algebra `S` of constant rank `Fintype.card ι` becomes split of constant rank
(`Algebra.IsFiniteSplit`) after base change to `FrameAlgebra R S ι`. -/
theorem isFiniteSplit_tensorProduct (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Algebra.IsFiniteSplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) :=
  .of_algEquiv (universalFrameEquiv h).symm

/-- A finite étale `R`-algebra `S` of constant rank `Fintype.card ι` becomes totally split
(`TauCeti.Algebra.IsTotallySplit`) after base change to `FrameAlgebra R S ι`. -/
theorem isTotallySplit_tensorProduct (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsTotallySplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) :=
  have := isFiniteSplit_tensorProduct h
  .of_isFiniteSplit

/-- Over a nontrivial ring `R`, the `|ι|` canonical slot maps `S →ₐ[R] FrameAlgebra R S ι` of a
finite étale algebra `S` of constant rank `Fintype.card ι` are pairwise distinct. -/
theorem slotAlgHom_injective_of_etale [Nontrivial R]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Function.Injective (slotAlgHom R S : ι → (S →ₐ[R] FrameAlgebra R S ι)) := by
  have htor := isFiniteEtaleTorsor h
  have := htor.faithfullyFlat
  have : Nontrivial (FrameAlgebra R S ι) :=
    (FaithfulSMul.algebraMap_injective R (FrameAlgebra R S ι)).nontrivial
  exact slotAlgHom_injective

end Etale

end FrameAlgebra

end TauCeti.Algebra
