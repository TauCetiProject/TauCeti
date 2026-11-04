/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Basic

/-!
# Positive-integer stretching of Lakshmibai–Seshadri paths

Multiplying the shape of an LS path by a positive integer preserves its directions and
breaks: the stabilizer quotient is unchanged, and every bond is multiplied by that integer.
Thus an integral break-chain remains integral. The resulting map `LSPath.stretch` is injective
and its realization is the linear dilation of the original path, not its concatenation power.

This constructs stretching on LS encodings. It does not assert that stretching is a strict
crystal morphism: in the similarity theorem a root operator corresponds to an iterated root
operator, rather than to a single root operator.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§4–5 (LS paths and stretching).
-/

public section

namespace TauCeti

open RootPairing

universe u v w

variable {ι : Type u} {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

namespace LSPath

variable {lam : M}

private theorem isAChain_map_nsmul {a : ℚ} (n : ℕ)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam))
    (f : SetRel.Hom {p : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} ×
        {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} |
        (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) p.2 p.1}
      {p : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b (n • lam)) w} ×
        {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b (n • lam)) w} |
        (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b (n • lam)) p.2 p.1})
    (hf : ∀ w, (f w).1 = w.1) (hC : IsAChain a lam C) :
    IsAChain a (n • lam) (C.map f) := by
  have hscaled (k : Fin C.length) : ∃ z : ℤ,
      a * P.reflectionBond b ((C k.castSucc).1 • n • lam) ((C k.succ).1 • n • lam) = z := by
    obtain ⟨z, hz⟩ := isAChain_iff_forall_reflectionBond.mp hC k
    have hb := P.reflectionBond_smul (b := b) (n : ℤ)
      ((C k.castSucc).1 • lam) ((C k.succ).1 • lam)
    simp only [Nat.cast_smul_eq_nsmul] at hb
    refine ⟨(n : ℤ) * z, ?_⟩
    rw [smul_comm (C k.castSucc).1 n lam, smul_comm (C k.succ).1 n lam, hb]
    push_cast
    rw [mul_left_comm a, hz]
  have hentry (j : Fin (C.length + 1)) : ((C.map f) j).1 = (C j).1 :=
    (congrArg Subtype.val (RelSeries.map_apply C f j)).trans (hf _)
  apply isAChain_iff_forall_reflectionBond.mpr
  -- `RelSeries.map` preserves length definitionally, so both chains use `Fin C.length`.
  intro k
  obtain ⟨z, hz⟩ := hscaled k
  refine ⟨z, ?_⟩
  exact (congrArg₂ (fun x y ↦ a * (P.reflectionBond b (x • n • lam) (y • n • lam) : ℚ))
    (hentry k.castSucc) (hentry k.succ)).trans hz

/-- Stretch an LS path by a positive integer, leaving its directions and break times unchanged.
All its break-chain bonds are multiplied by `n`. -/
noncomputable def stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) :
    LSPath P b (n • lam) := by
  have hw : P.wallIndices b (n • lam) = P.wallIndices b lam := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      (P.wallIndices_smul (b := b) (Int.natCast_ne_zero.mpr hn.ne') lam)
  let liftDir (w : {w // (weylCoxeterSystem P b).IsMinimalCosetRep
      (P.wallIndices b lam) w}) :
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b (n • lam)) w} :=
    ⟨w.1, hw.symm ▸ w.2⟩
  refine
    { length := π.length
      dir := fun j ↦ liftDir (π.dir j)
      time := π.time
      time_zero := π.time_zero
      time_last := π.time_last
      strictMono_time := π.strictMono_time
      dir_succ_ne := by
        intro j h
        apply π.dir_succ_ne j
        apply Subtype.ext
        exact congrArg (fun w : {w // (weylCoxeterSystem P b).IsMinimalCosetRep
          (P.wallIndices b (n • lam)) w} ↦ w.1) h
      exists_isAChain := ?_ }
  intro j
  obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j
  let D : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b (n • lam)) :=
    C.map ⟨liftDir, fun {x y} h ↦ by
      simpa only [Set.mem_ofPred_eq, liftDir, hw] using h⟩
  refine ⟨D, ?_, ?_, isAChain_map_nsmul n C _ (fun _ ↦ rfl) hC⟩
  · simpa only [D, RelSeries.head_map, RelHom.coeFn_mk] using congrArg liftDir hhead
  · simpa only [D, RelSeries.last_map, RelHom.coeFn_mk] using congrArg liftDir hlast

@[simp]
theorem length_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) :
    (π.stretch n hn).length = π.length := (rfl)

@[simp]
theorem dir_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n)
    (j : Fin ((π.stretch n hn).length + 1)) :
    ((π.stretch n hn).dir j).1 =
      (π.dir (j.cast (congrArg (· + 1) (π.length_stretch n hn)))).1 := (rfl)

@[simp]
theorem time_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n)
    (j : Fin ((π.stretch n hn).length + 2)) :
    (π.stretch n hn).time j =
      π.time (j.cast (congrArg (· + 2) (π.length_stretch n hn))) := (rfl)

@[simp]
theorem duration_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n)
    (j : Fin ((π.stretch n hn).length + 1)) :
    (π.stretch n hn).duration j =
      π.duration (j.cast (congrArg (· + 1) (π.length_stretch n hn))) := by
  simp only [duration_def, time_stretch]
  -- Casting a finite index preserves its value, so it commutes definitionally with
  -- `Fin.succ` and `Fin.castSucc` in the two endpoints of the duration.
  rfl

/-- Stretching keeps the list of Weyl-group directions unchanged. -/
@[simp↓]
theorem ofFn_dir_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) :
    (List.ofFn fun j ↦ ((π.stretch n hn).dir j).1) = List.ofFn fun j ↦ (π.dir j).1 := by
  rw [List.ofFn_congr (congrArg (· + 1) (π.length_stretch n hn))]
  simp only [dir_stretch, Fin.cast_cast, Fin.cast_eq_self]

/-- Stretching keeps the list of break times unchanged. -/
@[simp↓]
theorem ofFn_time_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) :
    List.ofFn (π.stretch n hn).time = List.ofFn π.time := by
  rw [List.ofFn_congr (congrArg (· + 2) (π.length_stretch n hn))]
  simp only [time_stretch, Fin.cast_cast, Fin.cast_eq_self]

/-- Stretching is injective on LS encodings, since it keeps all directions and breaks. -/
theorem stretch_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (fun π : LSPath P b lam ↦ π.stretch n hn) := by
  intro π ρ h
  apply LSPath.ext
  · have hd := congrArg (fun η ↦ List.ofFn fun j ↦ (η.dir j).1) h
    simp only [ofFn_dir_stretch] at hd
    exact List.map_injective_iff.mpr Subtype.val_injective
      (by simpa only [List.map_ofFn, Function.comp_def] using hd)
  · simpa only [ofFn_time_stretch] using congrArg (fun η ↦ List.ofFn η.time) h

/-- Stretching a straight LS path gives the straight LS path of the stretched shape. -/
@[simp]
theorem stretch_straight (lam : M) (n : ℕ) (hn : 0 < n) :
    (straight lam : LSPath P b lam).stretch n hn = straight (n • lam) := by
  apply LSPath.ext
  · apply List.map_injective_iff.mpr Subtype.val_injective
    simp only [List.map_ofFn, Function.comp_def, ofFn_dir_stretch, dir_straight]
    simp only [List.ofFn_const, length_straight]
  · simp only [ofFn_time_stretch, time_straight, length_straight, Fin.val_cast]

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The timed presentation of a stretched LS path has the same durations and dilated segments. -/
theorem timed_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) :
    (π.stretch n hn).timed 𝕜 f =
      (π.timed 𝕜 f).map (fun y ↦ (y.1, (n : 𝕜) • y.2)) := by
  simp only [timed_def, List.map_ofFn, Function.comp_def]
  rw [List.ofFn_congr (congrArg (· + 1) (π.length_stretch n hn))]
  congr 1
  funext j
  simp only [duration_stretch, dir_stretch, Fin.cast_cast, Fin.cast_eq_self,
    smul_comm _ n lam, map_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_comm]

/-- Realizing a stretched LS path gives the linear dilation of its realized path. -/
theorem toPLPath_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) :
    (π.stretch n hn).toPLPath 𝕜 f =
      (π.toPLPath 𝕜 f).map ((n : 𝕜) • LinearMap.id) := by
  simp only [toPLPath_def, timed_stretch, PLPath.map_ofSegments, List.map_map,
    Function.comp_def, LinearMap.smul_apply, LinearMap.id_apply]

/-- Stretching multiplies the endpoint by the stretching factor. -/
@[simp]
theorem endpoint_toPLPath_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n) :
    ((π.stretch n hn).toPLPath 𝕜 f).endpoint = (n : 𝕜) • (π.toPLPath 𝕜 f).endpoint := by
  simp [toPLPath_stretch]

end Realization

end LSPath

end TauCeti
