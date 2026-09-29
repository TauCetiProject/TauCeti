/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import TauCeti.RingTheory.KrullSchmidt.Existence

/-!
# Cancellation of direct summands

Azumaya's cancellation argument says that a module whose endomorphism ring is local cancels from
a finite direct sum.  Concretely, if `End(P)` is local and `M × P ≃ N × P`, then `M ≃ N`.
This is the one-summand form of Krull--Schmidt cancellation; iterating it over an indecomposable
decomposition cancels an arbitrary Krull--Schmidt module.

The proof uses block Gaussian elimination.  For an isomorphism

```text
       (a  b)
  e =  (c  d),
```

the lower-right block can be made invertible by a lower row operation.  Indeed, the lower-right
block equation for `e⁻¹e = 1` is `c' b + d' d = 1`.  Locality makes one summand invertible.  If
`d` is not already invertible, then `c' b` is invertible, and adding the lower row `c'` makes
`d + c' b` invertible.  Two triangular operations then diagonalize the resulting matrix; its other
diagonal block is the required isomorphism `M ≃ N`.

This theorem does not require finite generation.  Finiteness enters applications only in proving
that the common summand decomposes into pieces with local endomorphism rings.  A module of finite
length does: splitting off one indecomposable summand at a time, each with local endomorphism ring
by Fitting's lemma, cancels every common summand of finite length.  The modules being compared need
not have finite length themselves.

A consequence is that two surjections `s t : M → P` onto a projective module of finite length
differ by an automorphism of `M`: both split, `M ≃ ker s × P ≃ ker t × P`, and cancelling `P`
identifies the two kernels.

## Main results

* `TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isLocalRing_end`: a common summand with
  local endomorphism ring cancels from a linear equivalence.
* `TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isFiniteLength`: a common summand of finite
  length cancels from a linear equivalence.
* `TauCeti.exists_linearEquiv_comp_eq_of_surjective`: two surjections onto a projective module of
  finite length differ by an automorphism of their source.

## References

* G. Azumaya, *Corrections and supplementaries to my paper concerning Krull--Remak--Schmidt's
  theorem*, Nagoya Math. J. 1 (1950), 117--124.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10)(i).
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v w x

section Semiring

variable {A : Type u} [Semiring A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
variable {P : Type x} [AddCommGroup P] [Module A P]

/-- **Cancellation of a summand with local endomorphism ring.** If `End_A(P)` is local, a linear
equivalence `M × P ≃ N × P` induces a linear equivalence `M ≃ N`.

No finiteness assumption is needed.  The local endomorphism hypothesis already implies that `P`
is indecomposable; this is the one-summand cancellation step iterated in Krull--Schmidt--Azumaya
cancellation. -/
theorem nonempty_linearEquiv_of_prod_linearEquiv_of_isLocalRing_end
    [IsLocalRing (Module.End A P)]
    (h : Nonempty ((M × P) ≃ₗ[A] (N × P))) : Nonempty (M ≃ₗ[A] N) := by
  let _ : Nontrivial P := nontrivial_of_isLocalRing_end (A := A)
  let e := h.some
  let b : P →ₗ[A] N := (LinearMap.fst A N P).comp
    ((e : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P))
  let d : Module.End A P := (LinearMap.snd A N P).comp
    ((e : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P))
  let c' : N →ₗ[A] P := (LinearMap.snd A M P).comp
    ((e.symm : (N × P) →ₗ[A] (M × P)).comp (LinearMap.inl A N P))
  let d' : Module.End A P := (LinearMap.snd A M P).comp
    ((e.symm : (N × P) →ₗ[A] (M × P)).comp (LinearMap.inr A N P))
  have hinv : c'.comp b + d'.comp d = 1 := by
    ext p
    have he : e (0, p) = (b p, d p) := by
      simp only [b, d, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inr_apply,
        LinearMap.fst_apply, LinearMap.snd_apply]
    simp only [c', d', LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply, Module.End.one_apply]
    rw [← Prod.snd_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add, ← he,
      e.symm_apply_apply]
  have hright : IsUnit d ∨ IsUnit (d + c'.comp b) := by
    by_cases hd : IsUnit d
    · exact Or.inl hd
    right
    have hd'd : ¬IsUnit (d'.comp d) := by
      intro hunit
      apply hd
      exact isUnit_of_mul_isUnit_right (Module.End.mul_eq_comp d' d ▸ hunit)
    have hcb : IsUnit (c'.comp b) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hinv.symm ▸ isUnit_one) with hu | hu
      · exact hu
      · exact (hd'd hu).elim
    by_contra hsum
    have hnot : ¬IsUnit ((d + c'.comp b) + -d) :=
      IsLocalRing.nonunits_add hsum (by simpa using hd)
    apply hnot
    simpa [add_assoc] using hcb
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : (M × P) ≃ₗ[A] (N × P), IsUnit
      ((LinearMap.snd A N P).comp
        ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P))) := by
    rcases hright with hd | hd
    · exact ⟨e, hd⟩
    · refine ⟨e.trans ((LinearEquiv.refl A N).skewProd (LinearEquiv.refl A P) c'), ?_⟩
      convert hd using 1
      ext p
      simp [b, d, LinearMap.add_apply]
  let a₁ : M →ₗ[A] N := (LinearMap.fst A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inl A M P))
  let b₁ : P →ₗ[A] N := (LinearMap.fst A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P))
  let c₁ : M →ₗ[A] P := (LinearMap.snd A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inl A M P))
  let d₁ : Module.End A P := (LinearMap.snd A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P))
  let ed : P ≃ₗ[A] P := LinearEquiv.ofBijective d₁ ((Module.End.isUnit_iff d₁).mp he₁)
  let s : M →ₗ[A] N := a₁ - b₁.comp ((ed.symm : P →ₗ[A] P).comp c₁)
  let sourceShear : (M × P) ≃ₗ[A] (M × P) :=
    (LinearEquiv.refl A M).skewProd (LinearEquiv.refl A P)
      (-((ed.symm : P →ₗ[A] P).comp c₁))
  let targetShear : (N × P) ≃ₗ[A] (N × P) :=
    (LinearEquiv.prodComm A N P).trans
      (((LinearEquiv.refl A P).skewProd (LinearEquiv.refl A N)
        (-b₁.comp (ed.symm : P →ₗ[A] P))).trans (LinearEquiv.prodComm A P N))
  let diagonal := sourceShear.trans (e₁.trans targetShear)
  have he₁_apply (m : M) (p : P) : e₁ (m, p) =
      (a₁ m + b₁ p, c₁ m + d₁ p) := by
    rw [← Prod.fst_add_snd (m, p), map_add]
    simp only [a₁, b₁, c₁, d₁, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    rfl
  have hdiagonal (m : M) (p : P) : diagonal (m, p) = (s m, d₁ p) := by
    simp only [diagonal, sourceShear, targetShear, LinearEquiv.trans_apply,
      LinearEquiv.skewProd_apply, LinearEquiv.refl_apply, LinearEquiv.prodComm_apply]
    rw [he₁_apply]
    have hd_inv (x : P) : d₁ ((ed.symm : P →ₗ[A] P) x) = x := ed.apply_symm_apply x
    have hinv_d (x : P) : (ed.symm : P →ₗ[A] P) (d₁ x) = x := ed.symm_apply_apply x
    simp only [s, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      Prod.swap_prod_mk]
    apply Prod.ext
    · simp only [map_add, map_neg]
      rw [hd_inv, hinv_d]
      module
    · simp only [map_add, map_neg]
      rw [hd_inv]
      module
  have hs_injective : Function.Injective s := by
    intro m m' hmm'
    have hpair : diagonal (m, 0) = diagonal (m', 0) := by
      rw [hdiagonal, hdiagonal, hmm']
    exact congrArg Prod.fst (diagonal.injective hpair)
  have hs_surjective : Function.Surjective s := by
    intro n
    obtain ⟨⟨m, p⟩, hmp⟩ := diagonal.surjective (n, 0)
    rw [hdiagonal] at hmp
    exact ⟨m, congrArg Prod.fst hmp⟩
  exact ⟨LinearEquiv.ofBijective s ⟨hs_injective, hs_surjective⟩⟩

end Semiring

section Ring

variable {A : Type u} [Ring A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
variable {P : Type x} [AddCommGroup P] [Module A P]

/-- **Cancellation of a summand of finite length.** If `P` has finite length, a linear equivalence
`M × P ≃ N × P` induces a linear equivalence `M ≃ N`.

No finiteness is required of `M` and `N`. -/
theorem nonempty_linearEquiv_of_prod_linearEquiv_of_isFiniteLength (hP : IsFiniteLength A P)
    (h : Nonempty ((M × P) ≃ₗ[A] (N × P))) : Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hP
  -- Induct over the submodules of `P`, which are well founded because `P` is Artinian.
  suffices H : ∀ Q : Submodule A P, Nonempty ((M × Q) ≃ₗ[A] (N × Q)) → Nonempty (M ≃ₗ[A] N) by
    obtain ⟨e⟩ := h
    exact H ⊤ ⟨((LinearEquiv.refl A M).prodCongr Submodule.topEquiv).trans
      (e.trans ((LinearEquiv.refl A N).prodCongr Submodule.topEquiv.symm))⟩
  intro Q
  induction Q using WellFoundedLT.induction with
  | _ Q ih =>
  rintro ⟨e⟩
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · have : Unique Q := uniqueOfSubsingleton 0
    exact ⟨(LinearEquiv.prodUnique.symm.trans e).trans LinearEquiv.prodUnique⟩
  -- Split off an indecomposable summand `Q = N₁ ⊕ Q₁`; it has local endomorphism ring.
  obtain ⟨N₁, Q₁, hc, hN₁⟩ := exists_isCompl_isIndecomposableModule (A := A) (M := Q)
  have : IsLocalRing (Module.End A N₁) := isLocalRing_end_of_isIndecomposable
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩) hN₁
  let eQ : (Q₁ × N₁) ≃ₗ[A] Q :=
    (LinearEquiv.prodComm A Q₁ N₁).trans (Submodule.prodEquivOfIsCompl N₁ Q₁ hc)
  obtain ⟨e₁⟩ := nonempty_linearEquiv_of_prod_linearEquiv_of_isLocalRing_end
    ⟨((LinearEquiv.prodAssoc A M Q₁ N₁).trans ((LinearEquiv.refl A M).prodCongr eQ)).trans
      (e.trans ((LinearEquiv.prodAssoc A N Q₁ N₁).trans
        ((LinearEquiv.refl A N).prodCongr eQ)).symm)⟩
  -- The complement `Q₁` is a proper submodule of `Q`, so the induction hypothesis applies to it.
  have hlt : Q₁.map Q.subtype < Q := by
    have hQ₁ : Q₁ ≠ ⊤ := by
      rintro rfl
      exact (Submodule.nontrivial_iff_ne_bot.mp hN₁.nontrivial) (by simpa using hc.inf_eq_bot)
    simpa using Submodule.map_strictMono_of_injective Q.injective_subtype
      (lt_top_iff_ne_top.mpr hQ₁)
  let f := Submodule.equivMapOfInjective Q.subtype Q.injective_subtype Q₁
  exact ih _ hlt ⟨((LinearEquiv.refl A M).prodCongr f.symm).trans
    (e₁.trans ((LinearEquiv.refl A N).prodCongr f))⟩

/-- **Two surjections onto a projective module of finite length differ by an automorphism.** If
`P` is projective of finite length and `s t : M → P` are surjective, then `t ∘ θ = s` for some
automorphism `θ` of `M`. -/
theorem exists_linearEquiv_comp_eq_of_surjective [Module.Projective A P] (hP : IsFiniteLength A P)
    {s t : M →ₗ[A] P} (hs : Function.Surjective s) (ht : Function.Surjective t) :
    ∃ θ : M ≃ₗ[A] M, t ∘ₗ θ.toLinearMap = s := by
  -- Both surjections split, `M ≃ ker s × P ≃ ker t × P`, and `P` cancels.
  have split {u : M →ₗ[A] P} (hu : Function.Surjective u) :
      ∃ e : M ≃ₗ[A] (LinearMap.ker u × P), ∀ x, (e x).2 = u x := by
    obtain ⟨l, hl⟩ := Module.projective_lifting_property u LinearMap.id hu
    let e := Function.Exact.splitSurjectiveEquiv (LinearMap.exact_subtype_ker_map u)
      Subtype.val_injective ⟨l, hl⟩
    exact ⟨e.1, fun x ↦ (LinearMap.congr_fun e.2.2 x).symm⟩
  obtain ⟨es, hes⟩ := split hs
  obtain ⟨et, het⟩ := split ht
  obtain ⟨φ⟩ := nonempty_linearEquiv_of_prod_linearEquiv_of_isFiniteLength hP ⟨es.symm.trans et⟩
  refine ⟨es.trans ((φ.prodCongr (LinearEquiv.refl A P)).trans et.symm), ?_⟩
  ext x
  simp [← het, ← hes]

end Ring

end TauCeti
