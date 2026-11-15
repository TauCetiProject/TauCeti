/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.Module.LinearMap.EndQuotient
public import TauCeti.Algebra.Module.ProjectiveCover.Basic
public import TauCeti.RingTheory.Jacobson.Semiprimary
import TauCeti.RingTheory.SimpleModule.Basic

/-!
# Existence of projective covers over a semiprimary ring

`TauCeti/Algebra/Module/ProjectiveCover/Basic.lean` develops the projective cover of a module as a
*given* datum: it is unique, and it receives every projective presentation, but nothing there
produces one. This file supplies the existence theorem. Over a **semiprimary** ring — Mathlib's
`IsSemiprimaryRing`, a ring whose Jacobson radical is nilpotent and whose radical quotient is
semisimple, as a finite-dimensional algebra over a field is — **every** module has a projective
cover (`TauCeti.exists_isProjectiveCover`), with no finiteness hypothesis on the module.

Some hypothesis on the ring is genuinely needed: `ℤ ⧸ 2ℤ` has no projective cover as a `ℤ`-module,
although it has finite length.

## The construction

Write `J` for the radical and `M ↦ M ⧸ J • M` for passage to the radical quotient. Fix a free
module `N` with a surjection `p : N ↠ M` — the free module on the underlying set of `M` will do —
and let `q : N ⧸ J • N ↠ M ⧸ J • M` be the induced surjection. The cover is cut out of `N` by an
idempotent, in three steps.

* **The radical quotient is semisimple.** `N ⧸ J • N` is a module over `R ⧸ J`, which is a
  semisimple ring, so it is a semisimple `R ⧸ J`-module and hence a semisimple `R`-module
  (`TauCeti.isSemisimpleModule_quotient_jacobson_smul_top`). Therefore `ker q` has a complement
  `C`, and the projection onto `C` along `ker q` is an idempotent `ē` of `End (N ⧸ J • N)` with
  `range ē = C`.
* **The idempotent lifts.** Reduction of endomorphisms modulo `J • N` is a ring homomorphism
  `Ideal.endMapQ J N : End N →+* End (N ⧸ J • N)`. It is surjective because `N` is projective
  (`Ideal.endMapQ_surjective`), and every element of its kernel is nilpotent because `J` is
  (`Ideal.isNilpotent_of_mem_ker_endMapQ`): a map with image inside `J • N` has `k`-th power with
  image inside `J ^ k • N`. Mathlib's `exists_isIdempotentElem_eq_of_ker_isNilpotent` therefore
  lifts `ē` to an idempotent `e` of `End N`.
* **The cover is the image of the lift.** `P = range e` is a direct summand of the free module `N`,
  so it is projective, and `π = p|_P` is the cover. It is onto because its image spans `M` modulo
  `J • M` — that is what `ker ē = ker q` says — and `J • M` is superfluous
  (`TauCeti.isSuperfluous_smul_top_of_isNilpotent`, Nakayama for a nilpotent ideal). Its kernel is
  superfluous because an element of it reduces into `C ⊓ ker q = ⊥`, hence lies in `J • N`, hence,
  being fixed by `e`, lies in `J • P`.

Nilpotence of `J` is used twice, and differently: once to make `J • M` superfluous in an arbitrary
module — which is what removes every finiteness hypothesis, and is why a semiprimary ring covers
*all* modules and not only the finitely generated ones a semiperfect ring covers — and once to make
the kernel of the reduction map nil, which is what lets the idempotent lift.

Semiperfectness itself is `TauCeti.IsSemiperfectRing`, in
`TauCeti/RingTheory/Jacobson/Semiperfect.lean`: the second use of nilpotence above, made at the
level of the ring rather than of `End N`, is exactly the statement that a semiprimary ring is
semiperfect.

## Main statements

* `TauCeti.exists_isProjectiveCover_comp_subtype`: over a semiprimary ring, a surjection onto `M`
  from a projective module restricts to a projective cover of `M` on a submodule of its source.
* `TauCeti.exists_isProjectiveCover`: **every module over a semiprimary ring has a projective
  cover**, carried by a submodule of the free module on its underlying set.
* `TauCeti.exists_isProjectiveCover_of_finite`: the same statement for a module over a ring that is
  finite over an Artinian ring, such as a finite-dimensional algebra over a field; such a ring is
  semiprimary.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, §24 (semiperfect and semiprimary rings,
idempotent lifting, and projective covers), and I. Assem, D. Simson, A. Skowroński, *Elements of
the Representation Theory of Associative Algebras, Vol. 1*, Section I.5.
-/

public section

namespace TauCeti

universe u v w

section Semiprimary

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **A projective cover is cut out of any projective presentation by an idempotent.** Over a
semiprimary ring, a surjection `p : N ↠ M` from a projective module restricts to a projective cover
of `M` on a suitable submodule `P` of `N`; that cover property is all the statement records about
`P`. See the module docstring for how `P` is produced. -/
theorem exists_isProjectiveCover_comp_subtype [IsSemiprimaryRing R] {N : Type w} [AddCommGroup N]
    [Module R N] [Module.Projective R N] (p : N →ₗ[R] M) (hp : Function.Surjective p) :
    ∃ P : Submodule R N, IsProjectiveCover (p ∘ₗ P.subtype) := by
  -- The map induced by `p` on radical quotients is onto.
  let q := Submodule.mapQ _ _ p (Submodule.smul_top_le_comap_smul_top (Ring.jacobson R) p)
  have hq (n : N) : q (Submodule.Quotient.mk n) = Submodule.Quotient.mk (p n) :=
    Submodule.mapQ_apply _ _ p n
  have hqsurj : Function.Surjective q := LinearMap.range_eq_top.mp (by
    rw [Submodule.range_mapQ, LinearMap.range_eq_top.mpr hp, Submodule.map_top,
      Submodule.range_mkQ])
  -- The kernel of `q` splits off, because the radical quotient of `N` is semisimple.
  have hss := isSemisimpleModule_quotient_jacobson_smul_top R N
  obtain ⟨ebar, hebar, hqe, hdisj⟩ := q.exists_isIdempotentElem_comp_eq_disjoint_ker
  -- Lift `ebar`: the reduction map is onto with nil kernel.
  obtain ⟨e, he, hebar_eq⟩ :=
    Ideal.exists_isIdempotentElem_endMapQ_eq IsSemiprimaryRing.isNilpotent hebar
  have hebar_mk (n : N) : ebar (Submodule.Quotient.mk n) = Submodule.Quotient.mk (e n) := by
    rw [← hebar_eq]
    exact Ideal.endMapQ_mk _ N e n
  have hfix (x : N) (hx : x ∈ LinearMap.range e) : e x = x :=
    LinearMap.IsIdempotentElem.mem_range_iff he |>.mp hx
  -- Nakayama: the radical multiple of any module is superfluous in it.
  have hsuperM : IsSuperfluous (Ring.jacobson R • (⊤ : Submodule R M)) :=
    isSuperfluous_smul_top_of_isNilpotent IsSemiprimaryRing.isNilpotent
  refine ⟨LinearMap.range e, ?_, ?_, ?_⟩
  · -- `range e` is a direct summand of the projective module `N`, hence projective.
    exact Module.Projective.of_split (LinearMap.range e).subtype
      (e.codRestrict (LinearMap.range e) fun x => LinearMap.mem_range_self e x)
      (LinearMap.ext fun x => Subtype.ext (hfix _ x.2))
  · -- The image of `P` spans `M` modulo the superfluous `J • M`, hence is all of `M`.
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    refine hsuperM.eq_top_of_sup_eq_top (top_le_iff.mp fun x _ => ?_)
    obtain ⟨z, hz⟩ := hqsurj (Submodule.Quotient.mk x)
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hzz : (Submodule.Quotient.mk x : M ⧸ Ring.jacobson R • (⊤ : Submodule R M))
        = Submodule.Quotient.mk (p (e n)) := by
      rw [← hq, ← hebar_mk, ← hz, ← LinearMap.comp_apply q ebar, hqe]
    exact Submodule.mem_sup.mpr ⟨x - p (e n), (Submodule.Quotient.eq _).mp hzz,
      p (e n), Submodule.mem_map_of_mem ⟨n, rfl⟩, by abel⟩
  · -- An element of the kernel reduces into `range ebar ⊓ ker q = ⊥`, so lies in `J • N`, so in
    -- `J • P`.
    refine (isSuperfluous_smul_top_of_isNilpotent
      (M := ↥(LinearMap.range e)) IsSemiprimaryRing.isNilpotent).mono ?_
    rintro ⟨x, hx⟩ hker
    have hpx : p x = 0 := LinearMap.mem_ker.mp hker
    have hmemrange : (Submodule.Quotient.mk x : N ⧸ Ring.jacobson R • (⊤ : Submodule R N))
        ∈ LinearMap.range ebar := by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨Submodule.Quotient.mk y, hebar_mk y⟩
    have hmemker : (Submodule.Quotient.mk x : N ⧸ Ring.jacobson R • (⊤ : Submodule R N))
        ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, hq, hpx]
      exact Submodule.Quotient.mk_zero _
    have hxJN : x ∈ Ring.jacobson R • (⊤ : Submodule R N) :=
      (Submodule.Quotient.mk_eq_zero _).mp (Submodule.disjoint_def.mp hdisj _ hmemrange hmemker)
    rw [Submodule.mem_smul_top_iff]
    have hmap : x ∈ Submodule.map e (Ring.jacobson R • (⊤ : Submodule R N)) :=
      ⟨x, hxJN, hfix x hx⟩
    rwa [Submodule.map_smul'', Submodule.map_top] at hmap

variable (R M)

/-- **Every module over a semiprimary ring has a projective cover.**

The covering module is a submodule of the free module on the underlying set of `M`. No finiteness
is assumed of `M`: a semiprimary ring is left perfect, so it covers every module, not only the
finitely generated ones. -/
theorem exists_isProjectiveCover [IsSemiprimaryRing R] :
    ∃ P : Submodule R (M →₀ R),
      IsProjectiveCover (Finsupp.linearCombination R id ∘ₗ P.subtype) :=
  exists_isProjectiveCover_comp_subtype _ fun x => ⟨Finsupp.single x 1, by simp⟩

end Semiprimary

section FiniteOverArtinian

/-- **Every module over a ring finite over an Artinian ring has a projective cover.** Here `K` is an
Artinian ring acting on `A` compatibly with its multiplication, with `A` finite as a `K`-module; for
instance, `A` may be a finite-dimensional algebra over a field. No finiteness is required of the
module. -/
theorem exists_isProjectiveCover_of_finite (K : Type w) [Ring K] [IsArtinianRing K] (A : Type u)
    [Ring A] [Module K A] [IsScalarTower K A A] [Module.Finite K A] (V : Type v) [AddCommGroup V]
    [Module A V] :
    ∃ P : Submodule A (V →₀ A),
      IsProjectiveCover (Finsupp.linearCombination A id ∘ₗ P.subtype) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact exists_isProjectiveCover A V

end FiniteOverArtinian

end TauCeti
