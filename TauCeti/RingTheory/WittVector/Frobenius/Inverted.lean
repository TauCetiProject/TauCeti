/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.Colimit.Ring.Iterate
public import TauCeti.RingTheory.WittVector.Frobenius.Basic
public import TauCeti.RingTheory.WittVector.Ideal

/-!
# Frobenius-inverted Witt vectors

For a commutative ring `A`, the ring `W(A)[1/F]` of *Frobenius-inverted Witt vectors* is the
colimit of `W(A) → W(A) → ⋯` along the Witt vector Frobenius `F`
(`WittVector.FrobeniusInverted p A`, an instance of `RingHom.IterateColimit`). It is the ring of
sections over an affine open of the sheaf `W(𝒪_X)[1/F]` of a scheme `X` of characteristic `p`,
whose cohomology is the Frobenius-inverted Witt vector cohomology of Bhatt and Scholze. A ring map
`f : A →+* B` induces `W(f)[1/F]` (`WittVector.FrobeniusInverted.map`), and `F` acts on
`W(A)[1/F]` as the automorphism `RingHom.IterateColimit.ringEquiv`.

In characteristic `p` the Frobenius raises every Witt coordinate to its `p`-th power. Inverting it
therefore forgets exactly the nil phenomena of bounded exponent:

* `W(f)[1/F]` is injective exactly when the kernel of `f` is a nil ideal of bounded exponent, that
  is `a ^ p ^ c = 0` for all `a ∈ ker f` and a single `c`;
* `W(f)[1/F]` is surjective exactly when a uniform `p`-power `b ^ p ^ c` of every element of `B`
  lies in the image of `f`.

These are the same conditions under which `W(f)` is an isomorphism up to bounded torsion
(`WittVector.isoModSerre_isBoundedTorsion_map_iff`). The uniform exponent cannot be dropped: an
element of `W(A)` dies in `W(A)[1/F]` only if one power of `F` kills all of its coordinates at once.
Consequently `W(A)[1/F] → W(A ⧸ I)[1/F]` is an isomorphism for a nilpotent ideal `I`, for instance
the nilradical of a noetherian ring, and `W(f)[1/F]` is an isomorphism whenever `f` has an inverse
up to a power of the Frobenius: a ring map `g` in the other direction with `g ∘ f` and `f ∘ g` both
equal to `x ↦ x ^ p ^ N`. A universal homeomorphism need not have such an inverse: the quotient by
a nil ideal of unbounded exponent is one, yet its `W(f)[1/F]` is not injective. For a perfect ring
`A`, inverting `F` changes nothing, and this characterizes perfect rings. Finally, since
`F ∘ V = p`, the Frobenius becomes invertible once `p` is: the localization `W(A)[1/F][1/p]` is
`W(A)[1/p]`.

## Main definitions

* `WittVector.FrobeniusInverted p A`: the ring `W(A)[1/F]`.
* `WittVector.FrobeniusInverted.map f`: the ring map `W(A)[1/F] → W(B)[1/F]` induced by `f`.

## Main results

* `WittVector.FrobeniusInverted.of_eq_zero_iff_coeff_pow`: a Witt vector vanishes in
  `W(A)[1/F]` iff one power `p ^ k` kills all of its coordinates.
* `WittVector.FrobeniusInverted.of_bijective_iff_perfectRing`: `W(A) → W(A)[1/F]` is bijective
  iff `A` is perfect.
* `WittVector.FrobeniusInverted.map_injective_iff`,
  `WittVector.FrobeniusInverted.map_surjective_iff`,
  `WittVector.FrobeniusInverted.map_bijective_iff`: the criteria above.
* `WittVector.FrobeniusInverted.map_bijective_of_isNilpotent`: inverting `F` does not see a
  nilpotent ideal.
* `WittVector.FrobeniusInverted.map_bijective_of_comp_eq_pow`: `W(f)[1/F]` is bijective if `f`
  has an inverse up to the `p ^ N`-th power map.
* `WittVector.FrobeniusInverted.isLocalization_away_natCast`: inverting `p` in `W(A)[1/F]`
  inverts `p` in `W(A)`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), §11.5, Proposition 11.41 and its proof, Notation 11.42, Lemma 11.43.
* P. Berthelot, S. Bloch and H. Esnault, *On Witt vector cohomology for singular varieties*,
  Compos. Math. 143 (2007), Proposition 2.1.
-/

public noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime] (A : Type*) [CommRing A]

local notation "𝕎" => WittVector p

/-- The ring `W(A)[1/F]` of *Frobenius-inverted Witt vectors*: the colimit of
`W(A) → W(A) → ⋯` along the Witt vector Frobenius `F`. -/
abbrev FrobeniusInverted : Type _ :=
  (frobenius : 𝕎 A →+* 𝕎 A).IterateColimit

namespace FrobeniusInverted

open RingHom.IterateColimit

variable {p A} {B C : Type*} [CommRing B] [CommRing C]

/-! ### Functoriality -/

/-- The ring map `W(f)[1/F] : W(A)[1/F] → W(B)[1/F]` induced by a ring map `f : A →+* B`. -/
def map (f : A →+* B) : FrobeniusInverted p A →+* FrobeniusInverted p B :=
  RingHom.IterateColimit.map frobenius frobenius (WittVector.map (p := p) f)
    fun x ↦ map_frobenius f x

@[simp]
theorem map_mk (f : A →+* B) (n : ℕ) (x : 𝕎 A) :
    map f (RingHom.IterateColimit.mk frobenius n x) =
      RingHom.IterateColimit.mk frobenius n (WittVector.map f x) :=
  RingHom.IterateColimit.map_mk _ _ n x

@[simp]
theorem map_of (f : A →+* B) (x : 𝕎 A) :
    map f (of frobenius x) = of frobenius (WittVector.map f x) :=
  RingHom.IterateColimit.map_of _ _ x

@[simp]
theorem map_id : map (RingHom.id A) = RingHom.id (FrobeniusInverted p A) := by
  ext n x
  simp

theorem map_comp (f : A →+* B) (g : B →+* C) :
    map (p := p) (g.comp f) = (map g).comp (map f) := by
  have h : WittVector.map (p := p) (g.comp f) = (WittVector.map g).comp (WittVector.map f) :=
    RingHom.ext fun x ↦ WittVector.ext fun n ↦ by simp only [map_coeff, RingHom.comp_apply]
  simp only [map, h]
  exact RingHom.IterateColimit.map_comp _ _ _ _

/-- `W(f)[1/F]` commutes with the Frobenius automorphisms of `W(A)[1/F]` and `W(B)[1/F]`. -/
theorem map_ringEquiv (f : A →+* B) (z : FrobeniusInverted p A) :
    map f (ringEquiv frobenius z) = ringEquiv frobenius (map f z) :=
  RingHom.IterateColimit.map_ringEquiv _ _ z

/-- `W(f)[1/F]` is surjective when `f` is. -/
theorem map_surjective (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (map (p := p) f) :=
  (RingHom.IterateColimit.map_surjective_iff _ _).2 fun y ↦
    let ⟨x, hx⟩ := WittVector.map_surjective f hf y
    ⟨0, x, hx.symm⟩

/-! ### Characteristic `p` -/

section CharP

/-- **Vanishing in `W(A)[1/F]`.** In characteristic `p`, a Witt vector becomes zero after
inverting the Frobenius exactly when a single power `p ^ k` kills all of its coordinates. -/
theorem of_eq_zero_iff_coeff_pow [CharP A p] {x : 𝕎 A} :
    of frobenius x = 0 ↔ ∃ k : ℕ, ∀ n, x.coeff n ^ p ^ k = 0 := by
  simp only [RingHom.IterateColimit.of_eq_zero_iff, WittVector.ext_iff, iterate_frobenius_coeff,
    zero_coeff]

variable (p A) in
/-- **Inverting the Frobenius of a perfect ring changes nothing**, and only perfect rings have this
property: in characteristic `p`, the map `W(A) → W(A)[1/F]` is bijective exactly when `A` is
perfect. -/
theorem of_bijective_iff_perfectRing [CharP A p] :
    Function.Bijective (of (frobenius : 𝕎 A →+* 𝕎 A)) ↔ PerfectRing A p := by
  rw [RingHom.IterateColimit.of_bijective_iff, frobenius_eq_map_frobenius]
  refine ⟨fun h ↦ ⟨⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩⟩, fun h ↦ ?_⟩
  · -- Compare zeroth coordinates of Teichmüller representatives.
    have := h.1 (a₁ := teichmuller p a) (a₂ := teichmuller p b) <| by
      rw [map_teichmuller, map_teichmuller, frobenius_def, frobenius_def]
      exact congrArg _ hab
    simpa using congrArg (coeff · 0) this
  · obtain ⟨x, hx⟩ := h.2 (teichmuller p b)
    exact ⟨x.coeff 0, by simpa [frobenius_def] using congrArg (coeff · 0) hx⟩
  · exact ⟨WittVector.map_injective _ h.bijective_frobenius.1,
      WittVector.map_surjective _ h.bijective_frobenius.2⟩

/-- **Injectivity of `W(f)[1/F]`.** For a map `f : A →+* B` with `A` of characteristic `p`,
`W(f)[1/F]` is injective exactly when the kernel of `f` is a nil ideal of bounded exponent:
`a ^ p ^ c = 0` for a single `c` and all `a ∈ ker f`. -/
theorem map_injective_iff [CharP A p] (f : A →+* B) :
    Function.Injective (map (p := p) f) ↔ ∃ c : ℕ, ∀ a ∈ RingHom.ker f, a ^ p ^ c = 0 := by
  refine (RingHom.IterateColimit.map_injective_iff _ _).trans
    ⟨fun h ↦ ?_, fun ⟨c, hc⟩ x y ⟨k, hk⟩ ↦ ⟨c + k, ?_⟩⟩
  · -- If no single exponent works, choose `a c ∈ ker f` with `a c ^ p ^ c ≠ 0`; the Witt vector
    -- with coordinates `a` dies under `W(f)` but is not killed by any power of `F`.
    by_contra! hne
    choose a ha hne using hne
    obtain ⟨k, hk⟩ := h (WittVector.mk p a) 0 ⟨0, by
      ext n
      simp [map_coeff, RingHom.mem_ker.1 (ha n)]⟩
    apply hne k
    simpa [iterate_frobenius_coeff] using congrArg (coeff · k) hk
  · -- `Fᵏ x - Fᵏ y` lies in `W(ker f)`, which `F^c` kills.
    have hxy : frobenius^[k] x - frobenius^[k] y ∈ ideal p (RingHom.ker f) := by
      have hs : Function.Semiconj (WittVector.map f) frobenius^[k] frobenius^[k] :=
        Function.Semiconj.iterate_right (fun z ↦ map_frobenius (p := p) f z) k
      rw [← ker_map, RingHom.mem_ker, map_sub, hs x, hs y, hk, sub_self]
    have := iterate_frobenius_mem_ideal (I := ⊥) (fun a ha ↦ Ideal.mem_bot.2 (hc a ha)) hxy
    rw [ideal_bot, Ideal.mem_bot, iterate_map_sub, sub_eq_zero] at this
    rwa [Function.iterate_add_apply, Function.iterate_add_apply]

/-- **Surjectivity of `W(f)[1/F]`.** For a map `f : A →+* B` with `B` of characteristic `p`,
`W(f)[1/F]` is surjective exactly when a uniform `p`-power of every element of `B` lies in the
image of `f`. -/
theorem map_surjective_iff [CharP B p] (f : A →+* B) :
    Function.Surjective (map (p := p) f) ↔ ∃ c : ℕ, ∀ b, b ^ p ^ c ∈ f.range := by
  refine (RingHom.IterateColimit.map_surjective_iff _ _).trans ⟨fun h ↦ ?_, fun ⟨c, hc⟩ y ↦ ?_⟩
  · -- If no single exponent works, choose `b c` with `b c ^ p ^ c ∉ f(A)`; no power of `F`
    -- carries the Witt vector with coordinates `b` into the image of `W(f)`.
    by_contra! hne
    choose b hb using hne
    obtain ⟨k, x, hx⟩ := h (WittVector.mk p b)
    apply hb k
    have := congrArg (coeff · k) hx
    simp only [iterate_frobenius_coeff, map_coeff] at this
    exact ⟨_, this.symm⟩
  · -- The coordinates `y n ^ p ^ c` of `F^c y` all lie in the image of `f`.
    obtain ⟨x, hx⟩ := (mem_range_map_iff f (frobenius^[c] y)).2 fun n ↦ by
      rw [iterate_frobenius_coeff]
      exact hc _
    exact ⟨c, x, hx.symm⟩

/-- **Bijectivity of `W(f)[1/F]`.** For a map `f : A →+* B` of rings of characteristic `p`,
`W(f)[1/F]` is an isomorphism exactly when the kernel of `f` is a nil ideal of bounded exponent and
a uniform `p`-power of every element of `B` lies in the image of `f`. -/
theorem map_bijective_iff [CharP A p] [CharP B p] (f : A →+* B) :
    Function.Bijective (map (p := p) f) ↔
      (∃ c : ℕ, ∀ a ∈ RingHom.ker f, a ^ p ^ c = 0) ∧ ∃ c : ℕ, ∀ b, b ^ p ^ c ∈ f.range := by
  rw [Function.Bijective, map_injective_iff, map_surjective_iff]

/-- **Inverting the Frobenius does not see nilpotents.** In characteristic `p`, for a nilpotent
ideal `I` (for instance the nilradical of a noetherian ring), the map
`W(A)[1/F] → W(A ⧸ I)[1/F]` is an isomorphism. -/
theorem map_bijective_of_isNilpotent [CharP A p] {I : Ideal A} (hI : IsNilpotent I) :
    Function.Bijective (map (p := p) (Ideal.Quotient.mk I)) := by
  refine ⟨(map_injective_iff _).2 ?_, map_surjective _ Ideal.Quotient.mk_surjective⟩
  obtain ⟨m, hm⟩ := hI
  refine ⟨m, fun a ha ↦ ?_⟩
  rw [Ideal.mk_ker] at ha
  have hma : a ^ m = 0 := by
    simpa [hm] using Ideal.pow_mem_pow ha m
  exact pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hma

/-- **Maps invertible up to Frobenius.** If `f : A →+* B` has an inverse `g` up to the
`p ^ N`-th power map, `g (f a) = a ^ p ^ N` and `f (g b) = b ^ p ^ N`, then `W(f)[1/F]` is an
isomorphism. The hypothesis supplies the uniform exponent `N` that `map_bijective_iff` requires. A
ring map inducing a universal homeomorphism of spectra need not have such an inverse, for instance
the quotient by a nil ideal of unbounded exponent (see `map_injective_iff`). -/
theorem map_bijective_of_comp_eq_pow [CharP A p] [CharP B p] (f : A →+* B) (g : B →+* A) (N : ℕ)
    (hgf : ∀ a, g (f a) = a ^ p ^ N) (hfg : ∀ b, f (g b) = b ^ p ^ N) :
    Function.Bijective (map (p := p) f) :=
  (map_bijective_iff f).2
    ⟨⟨N, fun a ha ↦ by rw [← hgf, RingHom.mem_ker.1 ha, map_zero]⟩, ⟨N, fun b ↦ ⟨g b, hfg b⟩⟩⟩

end CharP

/-! ### Inverting `p` -/

/-- `p ^ n` times `F⁻ⁿ x` is the image of the Witt vector `Vⁿ x`. -/
theorem mk_mul_natCast_pow (n : ℕ) (x : 𝕎 A) :
    RingHom.IterateColimit.mk frobenius n x * (p : FrobeniusInverted p A) ^ n =
      of frobenius (verschiebung^[n] x) := by
  rw [of_eq_mk n, iterate_frobenius_iterate_verschiebung, map_mul, map_pow, map_natCast]

/-- **Inverting `p` after `F`.** In characteristic `p`, a localization of `W(A)[1/F]` away from
`p` is a localization of `W(A)` away from `p`: since `F ∘ V = V ∘ F = p`, the Frobenius is
already invertible on `W(A)[1/p]`, so `W(A)[1/p] = W(A)[1/F][1/p]`. -/
theorem isLocalization_away_natCast [CharP A p] (L : Type*) [CommRing L]
    [Algebra (FrobeniusInverted p A) L] [IsLocalization.Away (p : FrobeniusInverted p A) L] :
    letI := ((algebraMap (FrobeniusInverted p A) L).comp (of frobenius)).toAlgebra
    IsLocalization.Away (p : 𝕎 A) L := by
  let _ := ((algebraMap (FrobeniusInverted p A) L).comp (of frobenius)).toAlgebra
  have halg (x : 𝕎 A) : algebraMap (𝕎 A) L x = algebraMap _ L (of frobenius x) := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  refine IsLocalization.Away.mk _ ?_ (fun s ↦ ?_) (fun a b hab ↦ ?_)
  · rw [halg, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _
  · -- Write `s * p ^ n = mk m x`; then `s * p ^ (n + m) = of (Vᵐ x)`.
    obtain ⟨n, z, hz⟩ := IsLocalization.Away.surj (p : FrobeniusInverted p A) s
    obtain ⟨m, x, rfl⟩ := exists_eq_mk z
    refine ⟨n + m, verschiebung^[m] x, ?_⟩
    rw [halg, halg, map_natCast, pow_add, ← mul_assoc, hz, ← mk_mul_natCast_pow, map_mul,
      map_pow, map_natCast]
  · -- If `p ^ m * of a = p ^ m * of b`, then `Fᵏ (p ^ m * a) = Fᵏ (p ^ m * b)` for some `k`, and
    -- applying `Vᵏ` gives `p ^ (k + m) * a = p ^ (k + m) * b`.
    rw [halg, halg] at hab
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (p : FrobeniusInverted p A)) hab
    simp only at hm
    rw [← map_natCast (of frobenius), ← map_pow, ← map_mul, ← map_mul,
      RingHom.IterateColimit.of_eq_of_iff] at hm
    obtain ⟨k, hk⟩ := hm
    refine ⟨k + m, ?_⟩
    have := congrArg (verschiebung^[k]) hk
    simp only [iterate_verschiebung_iterate_frobenius] at this
    rw [pow_add]
    linear_combination this

end FrobeniusInverted

end WittVector
