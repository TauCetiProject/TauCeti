/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Module.ZMod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.RingTheory.RootsOfUnity.Connected

/-!
# Additive characters with connected coefficients

A nondegenerate character of `ℤ/p` identifies the `p`-th roots of unity of a commutative ring
with connected prime spectrum with the additive group of `ℤ/p`. Consequently every additive
character on an additive monoid killed by `p` comes from a unique homomorphism to `ℤ/p`.
Over a finite field the trace pairing identifies these homomorphisms with elements of the field,
as in Laumon,
*Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de Weil*, (0.2).
-/

public section

namespace AddChar

/-- For a ring with connected prime spectrum and a character `ψ` of `ℤ/p` with `ψ 1 - 1` a unit,
every additive character on an additive monoid killed by `p` is the composite of `ψ` and a
unique additive homomorphism to `ℤ/p`. -/
theorem existsUnique_compAddMonoidHom {p : ℕ} [Fact p.Prime] {R M : Type*} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] [AddMonoid M]
    (ψ : AddChar (ZMod p) R) (hψ : IsUnit (ψ 1 - 1)) (χ : AddChar M R)
    (hM : ∀ x : M, p • x = 0) :
    ∃! l : M →+ ZMod p, ψ.compAddMonoidHom l = χ := by
  have hψpow (a : ZMod p) : ψ a ^ p = 1 := by
    rw [← ψ.map_nsmul_eq_pow, ZModModule.char_nsmul_eq_zero p, ψ.map_zero_eq_one]
  have hχpow (x : M) : χ x ^ p = 1 := by
    rw [← χ.map_nsmul_eq_pow, hM, χ.map_zero_eq_one]
  have hp : IsUnit (p : R) := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime) (ψ 1 - 1) (1 : R)
    rw [sub_add_cancel, hψpow 1, one_pow] at hr
    have hr' : (p : R) * ((ψ 1 - 1) * r) = -(ψ 1 - 1) ^ p := by
      linear_combination -hr
    exact isUnit_of_mul_isUnit_left (hr' ▸ (hψ.pow p).neg)
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  let q := Ideal.Quotient.mk I
  have hroot : IsPrimitiveRoot (q (ψ 1)) p := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    exact orderOf_eq_prime (by rw [← map_pow, hψpow, map_one])
      (sub_ne_zero.mp (by simpa using (hψ.map q).ne_zero))
  have hval (a : ZMod p) : q (ψ a) = q (ψ 1) ^ a.val := by
    rw [← map_pow, ← map_nsmul_eq_pow, nsmul_one, ZMod.natCast_zmod_val]
  have hinj : Function.Injective ψ := by
    intro a b hab
    have he := congrArg q hab
    rw [hval a, hval b] at he
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun i : ℕ ↦ (i : ZMod p))
      (hroot.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) he)
  -- Find the exponent in the residue field, then lift equality of roots to the ring.
  have hsurj (x : M) : ∃ a : ZMod p, ψ a = χ x := by
    obtain ⟨i, hi, he⟩ := hroot.eq_pow_of_pow_eq_one (ξ := q (χ x)) (by
      rw [← map_pow, hχpow, map_one])
    refine ⟨i, q.injOn_pow_eq_one hp (hψpow _) (hχpow _) ?_⟩
    rwa [hval, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  choose l hl using hsurj
  let f : M →+ ZMod p :=
    { toFun := l
      map_zero' := hinj (by simp [hl])
      map_add' := fun a b ↦ hinj (by simp [map_add_eq_mul, hl]) }
  have hf : ψ.compAddMonoidHom f = χ := DFunLike.ext _ _ hl
  exact ⟨f, hf, fun _ hg ↦ ψ.compAddMonoidHom_injective_right hinj (hg.trans hf.symm)⟩

/-- If `ψ` is a nondegenerate additive character of `ℤ/p` into a ring with connected prime
spectrum, every additive character of the finite field `k` over `ℤ/p` is `x ↦ ψ(Tr(c * x))`
for exactly one `c : k`. -/
theorem existsUnique_apply_trace_mul {p : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] [Field k] [Finite k] [Algebra (ZMod p) k]
    (ψ : AddChar (ZMod p) R) (hψ : IsUnit (ψ 1 - 1)) (χ : AddChar k R) :
    ∃! c : k, ∀ x : k, ψ (Algebra.trace (ZMod p) k (c * x)) = χ x := by
  obtain ⟨l, hl, huniq⟩ := ψ.existsUnique_compAddMonoidHom hψ χ (ZModModule.char_nsmul_eq_zero p)
  let e := (Algebra.traceForm (ZMod p) k).toDual (traceForm_nondegenerate (ZMod p) k)
  obtain ⟨c, hc⟩ := e.surjective (l.toZModLinearMap p)
  have happ (a x : k) : e a x = Algebra.trace (ZMod p) k (a * x) := by
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]
  refine ⟨c, fun x ↦ ?_, fun d hd ↦ e.injective ?_⟩
  · rw [← happ, hc, AddMonoidHom.coe_toZModLinearMap]
    exact DFunLike.congr_fun hl x
  · rw [hc]
    have h : (e d).toAddMonoidHom = l := huniq _ (DFunLike.ext _ _ fun x ↦ by
      simpa only [compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe, happ] using hd x)
    exact LinearMap.ext fun x ↦ DFunLike.congr_fun h x

end AddChar
