/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.TensorProduct.Pi

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.Away.Lemmas
import TauCeti.Algebra.Algebra.Pi
import TauCeti.Algebra.Algebra.Subalgebra.Equalizer
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Idempotents.Refinement
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
import TauCeti.RingTheory.TensorProduct.Pi

/-!
# Equalizers of finite étale algebras

The equalizer of two algebra maps `f g : A →ₐ[R] B` between finite étale `R`-algebras is a finite
étale `R`-algebra (`AlgHom.etale_equalizer`, `AlgHom.finite_equalizer`). In particular, the
invariants of a finite étale algebra under a finite monoid acting by algebra endomorphisms form a
finite étale algebra (`TauCeti.FixedPoints.etale_subalgebra`,
`TauCeti.FixedPoints.finite_subalgebra`).
Geometrically, the affine coequalizer of two morphisms of finite étale `Spec R`-schemes, and the
invariant quotient of a finite étale `Spec R`-scheme by a finite group, are again finite étale.
The invariant quotients supply the quotients by finite groups that the axioms of a Galois category
require of finite étale covers.

## Main results

* `AlgHom.etale_equalizer`, `AlgHom.finite_equalizer`: equalizers of finite étale algebras are
  finite étale.
* `TauCeti.FixedPoints.etale_subalgebra`, `TauCeti.FixedPoints.finite_subalgebra`: invariants of
  a finite étale algebra under a finite monoid are finite étale.

## Implementation notes

The proof reduces to split algebras in three steps.

* Over a split base, an algebra map `φ : (ι → T) →ₐ[T] (κ → T)` has idempotent matrix entries
  `φ (Pi.single i 1) j`. Over the component of each atom of the Boolean algebra they generate
  (`TauCeti.completeOrthogonalIdempotents_prod_ite`), every entry is `0` or `1`, so `φ` is induced
  by a map `κ → ι`, and the equalizer of two such maps is the algebra of functions on a quotient
  of `ι`.
* If `A` and `B` have constant ranks, they both split after a faithfully flat finite étale base
  change (`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`). Flat base change commutes with
  equalizers (`AlgHom.tensorEqualizerEquiv`), and finite étaleness descends along faithfully flat
  maps.
* In general the ranks are locally constant, and the atoms of the idempotents cutting out their
  fibres decompose the base into components where both ranks are constant. Finite étaleness is
  local for such a decomposition (`TauCeti.Algebra.Etale.of_completeOrthogonalIdempotents`,
  `TauCeti.Module.Finite.of_completeOrthogonalIdempotents`).

The main results take `R`, `A` and `B` in one universe, as
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` does.

## References

* H. W. Lenstra, *Galois theory for schemes*, Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open TensorProduct

universe u

namespace AlgHom

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Finite étaleness of an equalizer is local for the decomposition of the base by the atoms of
finitely many idempotents `a x`: it suffices that over the component of every atom, the equalizer
of the base changes of `f` and `g` is finite étale. The components are flat localizations, and flat
base change commutes with equalizers (`AlgHom.tensorEqualizerEquiv`). -/
private theorem etale_and_finite_equalizer_of_prod_ite {T ι : Type*} [CommRing T] [Algebra T A]
    [Algebra T B] [Fintype ι] {a : ι → T} (ha : ∀ x, IsIdempotentElem (a x)) (f g : A →ₐ[T] B)
    (H : ∀ σ : ι → Bool,
      let T' := T ⧸ Ideal.span {1 - ∏ x, if σ x then a x else 1 - a x}
      Algebra.Etale T' (equalizer (Algebra.TensorProduct.map (AlgHom.id T' T') f)
          (Algebra.TensorProduct.map (AlgHom.id T' T') g)) ∧
        Module.Finite T' (equalizer (Algebra.TensorProduct.map (AlgHom.id T' T') f)
          (Algebra.TensorProduct.map (AlgHom.id T' T') g))) :
    Algebra.Etale T (equalizer f g) ∧ Module.Finite T (equalizer f g) := by
  classical
  have hF := TauCeti.completeOrthogonalIdempotents_prod_ite ha
  suffices H' : ∀ σ : ι → Bool,
      let T' := T ⧸ Ideal.span {1 - ∏ x, if σ x then a x else 1 - a x}
      Algebra.Etale T' (T' ⊗[T] equalizer f g) ∧ Module.Finite T' (T' ⊗[T] equalizer f g) from
    ⟨TauCeti.Algebra.Etale.of_completeOrthogonalIdempotents hF fun σ ↦ (H' σ).1,
      TauCeti.Module.Finite.of_completeOrthogonalIdempotents hF fun σ ↦ (H' σ).2⟩
  intro σ T'
  have : IsLocalization.Away (∏ x, if σ x then a x else 1 - a x) T' :=
    IsLocalization.Away.quotient_of_isIdempotentElem (hF.idem σ)
  have : Module.Flat T T' :=
    IsLocalization.flat T' (Submonoid.powers (∏ x, if σ x then a x else 1 - a x))
  let e := AlgHom.tensorEqualizerEquiv T' T' f g
  obtain ⟨h₁, h₂⟩ := H σ
  exact ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩

section Split

variable {T : Type*} [CommRing T]

/-- The equalizer of two algebra maps between split algebras whose matrix entries are all `0` or
`1` is finite étale: the maps are induced by maps `u v : κ → ι`, and the equalizer is the algebra
of functions on the quotient of `ι` by the relation identifying `u j` with `v j`. -/
private theorem etale_and_finite_equalizer_of_entries {ι κ : Type*} [_root_.Finite ι]
    [DecidableEq ι] (φ ψ : (ι → T) →ₐ[T] (κ → T))
    (hφ : ∀ i j, φ (Pi.single i 1) j = 0 ∨ φ (Pi.single i 1) j = 1)
    (hψ : ∀ i j, ψ (Pi.single i 1) j = 0 ∨ ψ (Pi.single i 1) j = 1) :
    Algebra.Etale T (equalizer φ ψ) ∧ Module.Finite T (equalizer φ ψ) := by
  cases subsingleton_or_nontrivial T
  · have : Subsingleton (equalizer φ ψ) := RingHom.codomain_trivial (algebraMap T _)
    let e : T ≃ₐ[T] equalizer φ ψ := AlgEquiv.ofBijective (Algebra.ofId T _)
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
    exact ⟨.of_equiv e, .equiv e.toLinearEquiv⟩
  obtain ⟨u, hu⟩ := exists_apply_eq_comp_of_entries φ hφ
  obtain ⟨v, hv⟩ := exists_apply_eq_comp_of_entries ψ hψ
  let r : ι → ι → Prop := fun a b ↦ ∃ j, u j = a ∧ v j = b
  let Ψ : (Quot r → T) →ₐ[T] (ι → T) := AlgHom.pi fun i ↦ Pi.evalAlgHom T (fun _ ↦ T) (Quot.mk r i)
  have hΨ (t : Quot r → T) : Ψ t ∈ equalizer φ ψ := by
    ext j
    simpa [hu, hv, Ψ] using congrArg t (Quot.sound ⟨j, rfl, rfl⟩)
  let e : (Quot r → T) ≃ₐ[T] equalizer φ ψ := AlgEquiv.ofBijective (Ψ.codRestrict _ hΨ) <| by
    refine ⟨fun t t' h ↦ funext <| Quot.ind fun i ↦ ?_, fun ⟨s, hs⟩ ↦ ?_⟩
    · simpa [Ψ] using congrFun (congrArg Subtype.val h) i
    · refine ⟨Quot.lift s ?_, Subtype.ext (funext fun i ↦ by simp [Ψ])⟩
      rintro _ _ ⟨j, rfl, rfl⟩
      simpa [hu, hv] using congrFun hs j
  exact ⟨.of_equiv e, .equiv e.toLinearEquiv⟩

/-- The equalizer of two algebra maps between split algebras is finite étale. Over the component
of each atom of the Boolean algebra generated by the matrix entries, all entries become `0` or `1`,
and the equalizer is computed by `etale_and_finite_equalizer_of_entries`. -/
private theorem etale_and_finite_equalizer_pi {ι κ : Type*} [_root_.Finite ι] [_root_.Finite κ]
    (φ ψ : (ι → T) →ₐ[T] (κ → T)) :
    Algebra.Etale T (equalizer φ ψ) ∧ Module.Finite T (equalizer φ ψ) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let a : Bool × ι × κ → T := fun x ↦ (bif x.1 then φ else ψ) (Pi.single x.2.1 1) x.2.2
  have ha (x : Bool × ι × κ) : IsIdempotentElem (a x) := by
    have hs : IsIdempotentElem (Pi.single x.2.1 1 : ι → T) := by
      rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
    exact (hs.map (bif x.1 then φ else ψ)).map (Pi.evalRingHom (fun _ ↦ T) x.2.2)
  refine etale_and_finite_equalizer_of_prod_ite ha φ ψ fun σ ↦ ?_
  intro T'
  -- In `T'` the atom becomes `1`, so every entry becomes `0` or `1` according to `σ`.
  have hT' (x : Bool × ι × κ) : algebraMap T T' (a x) = 0 ∨ algebraMap T T' (a x) = 1 := by
    have hfactor :=
      congrArg (Ideal.Quotient.mk (Ideal.span {1 - ∏ y, if σ y then a y else 1 - a y}))
        (TauCeti.ite_mul_prod_ite σ (ha x))
    rw [map_mul, TauCeti.Ideal.Quotient.mk_span_singleton_one_sub_self, mul_one] at hfactor
    rw [Ideal.Quotient.algebraMap_eq]
    split at hfactor
    · exact .inr hfactor
    · exact .inl (by simpa [sub_eq_self] using hfactor)
  let eι := Algebra.TensorProduct.piScalarRight T T' T' ι
  let eκ := Algebra.TensorProduct.piScalarRight T T' T' κ
  let e := eι.equalizerCongr eκ (Algebra.TensorProduct.map (AlgHom.id T' T') φ)
    (Algebra.TensorProduct.map (AlgHom.id T' T') ψ)
  obtain ⟨h₁, h₂⟩ := etale_and_finite_equalizer_of_entries
    ((eκ : (T' ⊗[T] (κ → T)) →ₐ[T'] (κ → T')).comp
      ((Algebra.TensorProduct.map (AlgHom.id T' T') φ).comp (eι.symm : (ι → T') →ₐ[T'] _)))
    ((eκ : (T' ⊗[T] (κ → T)) →ₐ[T'] (κ → T')).comp
      ((Algebra.TensorProduct.map (AlgHom.id T' T') ψ).comp (eι.symm : (ι → T') →ₐ[T'] _)))
    (fun i j ↦ by
      simpa [a, eι, eκ, Algebra.algebraMap_eq_smul_one] using
        hT' (true, i, j))
    (fun i j ↦ by
      simpa [a, eι, eκ, Algebra.algebraMap_eq_smul_one] using
        hT' (false, i, j))
  exact ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩

/-- The equalizer of two algebra maps between finite split algebras is finite étale. -/
private theorem etale_and_finite_equalizer_of_isFiniteSplit {A B : Type*} [CommRing A]
    [CommRing B] [Algebra T A] [Algebra T B] [Algebra.IsFiniteSplit T A]
    [Algebra.IsFiniteSplit T B] (f g : A →ₐ[T] B) :
    Algebra.Etale T (equalizer f g) ∧ Module.Finite T (equalizer f g) := by
  obtain ⟨m, ⟨eA⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T A
  obtain ⟨n, ⟨eB⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T B
  let e := eA.equalizerCongr eB f g
  obtain ⟨h₁, h₂⟩ := etale_and_finite_equalizer_pi
    ((eB : B →ₐ[T] (Fin n → T)).comp (f.comp (eA.symm : (Fin m → T) →ₐ[T] A)))
    ((eB : B →ₐ[T] (Fin n → T)).comp (g.comp (eA.symm : (Fin m → T) →ₐ[T] A)))
  exact ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩

end Split

/-- The equalizer of two algebra maps between finite étale algebras of constant ranks is finite
étale. Both algebras split after a faithfully flat finite étale base change
(`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`), flat base change commutes with
equalizers (`AlgHom.tensorEqualizerEquiv`), and finite étaleness descends. -/
private theorem etale_and_finite_equalizer_of_rankAtStalk_eq {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.Etale R A] [Module.Finite R A]
    [Algebra.Etale R B] [Module.Finite R B] {m n : ℕ} (hA : Module.rankAtStalk (R := R) A = m)
    (hB : Module.rankAtStalk (R := R) B = n) (f g : A →ₐ[R] B) :
    Algebra.Etale R (equalizer f g) ∧ Module.Finite R (equalizer f g) := by
  obtain ⟨T₁, _, _, _, _, _, _⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hA
  have hB₁ : Module.rankAtStalk (R := T₁) (T₁ ⊗[R] B) = n := by
    ext p
    rw [Module.rankAtStalk_baseChange, hB, Pi.natCast_apply, Pi.natCast_apply]
  obtain ⟨T₂, _, _, _, _, _, _⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hB₁
  let : Algebra R T₂ := ((algebraMap T₁ T₂).comp (algebraMap R T₁)).toAlgebra
  have : IsScalarTower R T₁ T₂ := .of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat R T₂ := .trans R T₁ T₂
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] A) :=
    .of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ A)
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] B) :=
    .of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ B)
  let e := AlgHom.tensorEqualizerEquiv T₂ T₂ f g
  obtain ⟨h₁, h₂⟩ := etale_and_finite_equalizer_of_isFiniteSplit
    (Algebra.TensorProduct.map (AlgHom.id T₂ T₂) f) (Algebra.TensorProduct.map (AlgHom.id T₂ T₂) g)
  have : Algebra.Etale T₂ (T₂ ⊗[R] equalizer f g) := .of_equiv e.symm
  have : Module.Finite T₂ (T₂ ⊗[R] equalizer f g) := .equiv e.symm.toLinearEquiv
  exact ⟨.of_etale_tensorProduct_of_faithfullyFlat T₂,
    .of_finite_tensorProduct_of_faithfullyFlat T₂⟩

/-- The equalizer of two algebra maps between finite étale algebras is finite étale. The ranks of
the two algebras are locally constant, so the atoms of the idempotents cutting out their fibres
decompose the base into components over which both ranks are constant. -/
private theorem etale_and_finite_equalizer {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [Module.Finite R A] [Algebra.Etale R B]
    [Module.Finite R B] (f g : A →ₐ[R] B) :
    Algebra.Etale R (equalizer f g) ∧ Module.Finite R (equalizer f g) := by
  classical
  have : Module.FinitePresentation R A := .of_finite_of_finitePresentation R A
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  obtain ⟨N, hNA, hNB⟩ : ∃ N, (∀ p, Module.rankAtStalk (R := R) A p ≤ N) ∧
      ∀ p, Module.rankAtStalk (R := R) B p ≤ N := by
    obtain ⟨NA, hNA⟩ :=
      (Module.isLocallyConstant_rankAtStalk (R := R) (M := A)).range_finite.bddAbove
    obtain ⟨NB, hNB⟩ :=
      (Module.isLocallyConstant_rankAtStalk (R := R) (M := B)).range_finite.bddAbove
    exact ⟨max NA NB, fun p ↦ (hNA ⟨p, rfl⟩).trans (le_max_left _ _),
      fun p ↦ (hNB ⟨p, rfl⟩).trans (le_max_right _ _)⟩
  choose εA hεA hεA' using fun k : Fin (N + 1) ↦
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
      ((Module.isLocallyConstant_rankAtStalk (R := R) (M := A)).isClopen_fiber (k : ℕ))
  choose εB hεB hεB' using fun k : Fin (N + 1) ↦
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
      ((Module.isLocallyConstant_rankAtStalk (R := R) (M := B)).isClopen_fiber (k : ℕ))
  let a : Fin (N + 1) ⊕ Fin (N + 1) → R := Sum.elim εA εB
  have ha (x : Fin (N + 1) ⊕ Fin (N + 1)) : IsIdempotentElem (a x) := by
    cases x
    · exact hεA _
    · exact hεB _
  refine etale_and_finite_equalizer_of_prod_ite ha f g fun σ ↦ ?_
  intro T'
  -- Every prime of `T'` lies over the component of the atom, where the ranks of `A` and `B` are
  -- read off from the atom.
  have hσ (q : PrimeSpectrum T') : ∀ x, a x ∉ (q.comap (algebraMap R T')).asIdeal ↔ σ x := by
    have h0 : algebraMap R T' (1 - ∏ x, if σ x then a x else 1 - a x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    exact fun x ↦ TauCeti.notMem_iff_of_one_sub_prod_ite_mem σ
      (Ideal.mem_comap.mpr (h0 ▸ q.asIdeal.zero_mem)) (ha x)
  -- A rank bounded by `N` whose fibres are the basic open sets of elements `ε k` that every prime
  -- of `T'` sees uniformly is the same at all primes under primes of `T'`.
  have hconst (r : PrimeSpectrum R → ℕ) (ε : Fin (N + 1) → R) (hN : ∀ p, r p ≤ N)
      (hε : ∀ k : Fin (N + 1), r ⁻¹' {(k : ℕ)} = (PrimeSpectrum.basicOpen (ε k) : Set _))
      (hT' : ∀ (q q' : PrimeSpectrum T') k, ε k ∉ (q.comap (algebraMap R T')).asIdeal ↔
        ε k ∉ (q'.comap (algebraMap R T')).asIdeal) (q q' : PrimeSpectrum T') :
      r (q.comap (algebraMap R T')) = r (q'.comap (algebraMap R T')) := by
    have hmem (p : PrimeSpectrum R) (k : Fin (N + 1)) : r p = k ↔ ε k ∉ p.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using congrArg (p ∈ ·) (hε k)
    let k : Fin (N + 1) := ⟨_, Nat.lt_succ_of_le (hN (q.comap (algebraMap R T')))⟩
    exact ((hmem _ k).mpr ((hT' q q' k).mp ((hmem _ k).mp rfl))).symm
  obtain ⟨m, hm⟩ := TauCeti.Module.exists_rankAtStalk_tensorProduct_eq (M := A) (T' := T') <|
    hconst _ εA hNA hεA' fun q q' k ↦ (hσ q (.inl k)).trans (hσ q' (.inl k)).symm
  obtain ⟨n, hn⟩ := TauCeti.Module.exists_rankAtStalk_tensorProduct_eq (M := B) (T' := T') <|
    hconst _ εB hNB hεB' fun q q' k ↦ (hσ q (.inr k)).trans (hσ q' (.inr k)).symm
  exact etale_and_finite_equalizer_of_rankAtStalk_eq hm hn _ _

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra.Etale R A] [Module.Finite R A] [Algebra.Etale R B] [Module.Finite R B]

/-- **The equalizer of two algebra maps between finite étale algebras is étale.** -/
instance etale_equalizer (f g : A →ₐ[R] B) : Algebra.Etale R (equalizer f g) :=
  (etale_and_finite_equalizer f g).1

/-- The equalizer of two algebra maps between finite étale algebras is a finite module. -/
instance finite_equalizer (f g : A →ₐ[R] B) : Module.Finite R (equalizer f g) :=
  (etale_and_finite_equalizer f g).2

end

end AlgHom

namespace TauCeti.FixedPoints

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [Monoid G]
  [MulSemiringAction G S] [SMulCommClass G R S]

variable [Algebra.Etale R S] [Module.Finite R S] [Finite G]

/-- **The invariants of a finite étale algebra under a finite monoid of algebra endomorphisms form
an étale algebra.** -/
instance etale_subalgebra : Algebra.Etale R (FixedPoints.subalgebra R S G) := by
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin G
  rw [subalgebra_eq_equalizer G σ.symm.surjective]
  infer_instance

/-- The invariants of a finite étale algebra under a finite monoid of algebra endomorphisms form a
finite module. -/
instance finite_subalgebra : Module.Finite R (FixedPoints.subalgebra R S G) := by
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin G
  rw [subalgebra_eq_equalizer G σ.symm.surjective]
  infer_instance

end TauCeti.FixedPoints
