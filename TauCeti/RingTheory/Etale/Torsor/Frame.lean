/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TotallySplit
public import TauCeti.RingTheory.Etale.Torsor.Descent
public import TauCeti.RingTheory.Unramified.Frame
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The frame algebra of a finite étale algebra is a splitting torsor

Let `S` be an `R`-algebra which becomes split of rank `|ι|` after a faithfully flat extension
`R → T`, that is `T ⊗[R] S ≃ₐ[T] (ι → T)`. Then the frame algebra
`TauCeti.Algebra.FrameAlgebra R S ι` of `ι`-tuples of pairwise distinct points of `Spec S` is a
finite étale `Equiv.Perm ι`-torsor over `R`
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`), and the universal frame
`FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` is an isomorphism
(`TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi`), so `S` becomes finite split
after base change to `FrameAlgebra R S ι`
(`TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct_of_algEquiv_pi`).

Indeed, forming frame algebras commutes with base change
(`TauCeti.Algebra.FrameAlgebra.baseChangeEquiv`), so `T ⊗[R] FrameAlgebra R S ι` is the frame
algebra of the split algebra `ι → T`, which is the trivial torsor `Equiv.Perm ι → T`
(`TauCeti.Algebra.FrameAlgebra.permEquiv`) and has a bijective universal frame
(`TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_pi`); both being a torsor
(`TauCeti.Algebra.IsFiniteEtaleTorsor.of_baseChange_algEquiv_pi`) and bijectivity of the universal
frame (`TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_baseChange_iff`) descend along
faithfully flat extensions.

Every finite étale algebra `S` of constant rank `Fintype.card ι` is split by a faithfully flat
finite étale extension (Mathlib's `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`), so its
frame algebra is a finite étale `Perm ι`-torsor of constant rank `(|ι|)!`
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`,
`TauCeti.Algebra.FrameAlgebra.rankAtStalk_eq_factorial`) that splits `S` via its universal frame
(`TauCeti.Algebra.FrameAlgebra.universalFrameEquiv`,
`TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct`). It is the ring-theoretic Galois
closure of `S`: for a finite separable field extension `L / K` of degree `n` with Galois closure
`M`, it is a product of copies of `M` of total `K`-dimension `n!`. The splitting cover is stated
for `S` in the universe of `R`. A finite algebra is isomorphic to one in that universe (`Shrink`),
and both the frame algebra and its universal frame are invariant under isomorphisms
(`TauCeti.Algebra.FrameAlgebra.congr`,
`TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_congr_iff`), so the results hold for `S` in
any universe.

## Main definitions

* `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv`: the universal frame
  `FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` for a finite étale
  `R`-algebra `S` of constant rank `Fintype.card ι`.

## Main results

* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`: the frame algebra of an
  algebra split by a faithfully flat extension is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct_of_algEquiv_pi`: an algebra split by a
  faithfully flat extension becomes finite split over its frame algebra.
* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`: the frame algebra of a finite étale algebra
  of constant rank `Fintype.card ι` is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame`: the universal frame of a finite étale
  algebra of constant rank `Fintype.card ι` is bijective.
* `TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct`: a finite étale algebra of constant
  rank `Fintype.card ι` becomes finite split after base change to its frame algebra.
* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_finrank_eq`,
  `TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct_of_finrank_eq`,
  `TauCeti.Algebra.FrameAlgebra.finrank_eq_factorial`: specializations over a field.

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

/-- **A locally split algebra is finite split over its frame algebra.** If `S` becomes isomorphic
to `ι → T` after a faithfully flat extension `R → T`, then `FrameAlgebra R S ι ⊗[R] S` is finite
split over `FrameAlgebra R S ι` via the universal frame. -/
theorem isFiniteSplit_tensorProduct_of_algEquiv_pi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    Algebra.IsFiniteSplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) :=
  .of_algEquiv (universalFrameEquivOfAlgEquivPi T e).symm

end LocallySplit

section ConstantRank

/-- Over a nontrivial ring `R`, a finite étale `R`-algebra `S` in the same universe of constant
rank `Fintype.card ι` admits a faithfully flat `R`-algebra `T` with `T ⊗[R] S ≃ₐ[T] (ι → T)`. -/
private theorem exists_faithfullyFlat_algEquiv_pi {R S : Type u} [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Module.FaithfullyFlat R T),
      Nonempty (T ⊗[R] S ≃ₐ[T] (ι → T)) := by
  obtain ⟨T, _, _, _, _, _, _⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale h
  obtain ⟨m, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T (T ⊗[R] S)
  have : Nontrivial T := (FaithfulSMul.algebraMap_injective R T).nontrivial
  obtain rfl : m = Fintype.card ι := by
    simpa using f.toLinearEquiv.finrank_eq.symm.trans
      (TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq h)
  exact ⟨T, _, _, ‹_›,
    ⟨f.trans (AlgEquiv.piCongrLeft' T (fun _ ↦ T) (Fintype.equivFin ι).symm)⟩⟩

/-- `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor` for `R` and `S` in the same universe, in
which Mathlib's splitting cover `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` applies. -/
private theorem isFiniteEtaleTorsor_aux {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) := by
  cases subsingleton_or_nontrivial R
  · infer_instance
  obtain ⟨T, _, _, _, ⟨f⟩⟩ := exists_faithfullyFlat_algEquiv_pi h
  exact isFiniteEtaleTorsor_of_algEquiv_pi T f

/-- **The frame algebra is a torsor.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, the frame algebra of `ι`-tuples of pairwise distinct points of `S` is a finite
étale `Perm ι`-torsor over `R`. -/
theorem isFiniteEtaleTorsor {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) := by
  -- The finite algebra `S` is isomorphic to an algebra in the universe of `R`, and the frame
  -- algebra is invariant under isomorphisms.
  have : Small.{u} S := Module.Finite.small R S
  let e : Shrink.{u} S ≃ₐ[R] S := Shrink.algEquiv R S
  have : Algebra.Etale R (Shrink.{u} S) := .of_equiv e.symm
  have : Module.Finite R (Shrink.{u} S) := .equiv e.symm.toLinearEquiv
  have := isFiniteEtaleTorsor_aux (ι := ι)
    ((Module.rankAtStalk_eq_of_equiv e.toLinearEquiv).trans h)
  exact .of_algEquiv (FrameAlgebra.congr ι e) (FrameAlgebra.congr_smul e)

/-- The frame algebra of a finite étale `R`-algebra `S` of constant rank `Fintype.card ι` has
stalk rank `(Fintype.card ι).factorial` at every prime of `R`. -/
theorem rankAtStalk_eq_factorial {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (FrameAlgebra R S ι) p = (Fintype.card ι).factorial := by
  have := isFiniteEtaleTorsor h
  rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Equiv.Perm ι), Nat.card_eq_fintype_card,
    Fintype.card_perm]

/-- `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame` for `R` and `S` in the same
universe. -/
private theorem bijective_universalFrame_aux {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Function.Bijective (universalFrame R S ι) := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton (FrameAlgebra R S ι) := Module.subsingleton R _
    have : Subsingleton (FrameAlgebra R S ι ⊗[R] S) := Module.subsingleton R _
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨T, _, _, _, ⟨f⟩⟩ := exists_faithfullyFlat_algEquiv_pi h
  exact bijective_universalFrame_of_algEquiv_pi T f

/-- **The universal frame of a finite étale algebra of constant rank is bijective.** For a finite
étale `R`-algebra `S` of constant rank `Fintype.card ι`, the universal frame
`FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` is bijective. -/
theorem bijective_universalFrame {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Function.Bijective (universalFrame R S ι) := by
  have : Small.{u} S := Module.Finite.small R S
  let e : Shrink.{u} S ≃ₐ[R] S := Shrink.algEquiv R S
  have : Algebra.Etale R (Shrink.{u} S) := .of_equiv e.symm
  have : Module.Finite R (Shrink.{u} S) := .equiv e.symm.toLinearEquiv
  exact (bijective_universalFrame_congr_iff e).mpr
    (bijective_universalFrame_aux ((Module.rankAtStalk_eq_of_equiv e.toLinearEquiv).trans h))

/-- **The universal frame isomorphism.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, the universal frame gives a canonical `FrameAlgebra R S ι`-algebra isomorphism
`FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)`. -/
noncomputable def universalFrameEquiv {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  AlgEquiv.ofBijective _ (bijective_universalFrame h)

/-- The underlying map of `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv` is
`TauCeti.Algebra.FrameAlgebra.universalFrame`. -/
theorem coe_universalFrameEquiv {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    ⇑(universalFrameEquiv h) = universalFrame R S ι := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv` sends `p ⊗ s` to
`i ↦ p * singleAlgHom R S i s`. -/
@[simp]
theorem universalFrameEquiv_tmul {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) (p : FrameAlgebra R S ι) (s : S)
    (i : ι) :
    universalFrameEquiv h (p ⊗ₜ s) i = p * singleAlgHom R S i s :=
  universalFrame_tmul p s i

/-- **A finite étale algebra of constant rank splits over its frame algebra.** For a finite étale
`R`-algebra `S` of constant rank `Fintype.card ι`, the base change `FrameAlgebra R S ι ⊗[R] S` is
finite split over `FrameAlgebra R S ι`. -/
theorem isFiniteSplit_tensorProduct {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Algebra.IsFiniteSplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) :=
  .of_algEquiv (universalFrameEquiv h).symm

end ConstantRank

section Field

variable {K : Type u} {S : Type*} [Field K] [CommRing S] [Algebra K S] [Algebra.Etale K S]
  {ι : Type*} [Fintype ι]

/-- Over a field `K`, an étale `K`-algebra `S` with `Module.finrank K S = Fintype.card ι` has
constant stalk rank `Fintype.card ι`. -/
private theorem rankAtStalk_eq_of_finrank_eq (h : Module.finrank K S = Fintype.card ι) :
    Module.rankAtStalk (R := K) S = Fintype.card ι := by
  have := Algebra.FormallyUnramified.finite_of_free (R := K) (S := S)
  ext p
  simp [Module.rankAtStalk_eq_finrank_of_free, h]

variable [DecidableEq ι]

/-- Over a field `K`, the frame algebra of an étale `K`-algebra `S` of `K`-dimension
`Fintype.card ι` is a finite étale `Equiv.Perm ι`-torsor over `K`. -/
theorem isFiniteEtaleTorsor_of_finrank_eq (h : Module.finrank K S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) K (FrameAlgebra K S ι) := by
  have := Algebra.FormallyUnramified.finite_of_free (R := K) (S := S)
  exact isFiniteEtaleTorsor (rankAtStalk_eq_of_finrank_eq h)

/-- Over a field `K`, the universal frame of an étale `K`-algebra `S` of `K`-dimension
`Fintype.card ι` is a `FrameAlgebra K S ι`-algebra isomorphism. -/
noncomputable def universalFrameEquivOfFinrankEq (h : Module.finrank K S = Fintype.card ι) :
    FrameAlgebra K S ι ⊗[K] S ≃ₐ[FrameAlgebra K S ι] (ι → FrameAlgebra K S ι) :=
  haveI := Algebra.FormallyUnramified.finite_of_free (R := K) (S := S)
  universalFrameEquiv (rankAtStalk_eq_of_finrank_eq h)

/-- The underlying map of `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfFinrankEq` is
`TauCeti.Algebra.FrameAlgebra.universalFrame`. -/
theorem coe_universalFrameEquivOfFinrankEq (h : Module.finrank K S = Fintype.card ι) :
    ⇑(universalFrameEquivOfFinrankEq h) = universalFrame K S ι := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfFinrankEq` sends `p ⊗ s` to
`i ↦ p * singleAlgHom K S i s`. -/
@[simp]
theorem universalFrameEquivOfFinrankEq_tmul (h : Module.finrank K S = Fintype.card ι)
    (p : FrameAlgebra K S ι) (s : S) (i : ι) :
    universalFrameEquivOfFinrankEq h (p ⊗ₜ s) i = p * singleAlgHom K S i s :=
  universalFrame_tmul p s i

/-- Over a field `K`, an étale `K`-algebra `S` of `K`-dimension `Fintype.card ι` becomes finite
split after base change to `FrameAlgebra K S ι`. -/
theorem isFiniteSplit_tensorProduct_of_finrank_eq (h : Module.finrank K S = Fintype.card ι) :
    Algebra.IsFiniteSplit (FrameAlgebra K S ι) (FrameAlgebra K S ι ⊗[K] S) :=
  .of_algEquiv (universalFrameEquivOfFinrankEq h).symm

/-- Over a field `K`, the frame algebra of an étale `K`-algebra `S` of `K`-dimension
`Fintype.card ι` has `K`-dimension `(Fintype.card ι).factorial`. -/
theorem finrank_eq_factorial (h : Module.finrank K S = Fintype.card ι) :
    Module.finrank K (FrameAlgebra K S ι) = (Fintype.card ι).factorial := by
  have := Algebra.FormallyUnramified.finite_of_free (R := K) (S := S)
  exact TauCeti.Module.finrank_eq_of_rankAtStalk_eq (funext (rankAtStalk_eq_factorial
    (rankAtStalk_eq_of_finrank_eq h)))

end Field

end FrameAlgebra

end TauCeti.Algebra
